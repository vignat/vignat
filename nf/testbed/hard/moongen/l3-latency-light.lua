local mg     = require "moongen"
local memory = require "memory"
local device = require "device"
local ts     = require "timestamping"
local filter = require "filter"
local hist   = require "histogram"
local stats  = require "stats"
local timer  = require "timer"
local log    = require "log"

-- set addresses here
local DST_MAC		= "90:e2:ba:55:14:11" -- resolved via ARP on GW_IP or DST_IP, can be overriden with a string here
local SRC_IP_BASE	= "192.168.6.5" -- actual address will be SRC_IP_BASE + random(0, flows)
local DST_IP		= "192.168.4.10"
local SRC_PORT		= 1
local DST_PORT		= 319
local START_PROBE_PORT	= 64000
local N_PROBE_FLOWS	= 1000

function configure(parser)
	parser:description("Generates UDP traffic and measure latencies. Edit the source to modify constants like IPs.")
	parser:argument("txDev", "Device to transmit from."):convert(tonumber)
	parser:argument("rxDev", "Device to receive from."):convert(tonumber)
	parser:option("-r --rate", "Transmit rate in Mbit/s."):default(10000):convert(tonumber)
	parser:option("-s --size", "Packet size."):default(60):convert(tonumber)
	parser:option("-u --upheat", "Heatup time before beginning of latency measurement"):default(2):convert(tonumber)
	parser:option("-t --timeout", "Time to run the test"):default(0):convert(tonumber)
end

function setRate(queue, packetSize, rate_mbps)
	queue:setRate(rate_mbps - (packetSize + 4) * 8 / 1000);
end

function master(args)
	txDev = device.config{port = args.txDev, rxQueues = 3, txQueues = 3}
	rxDev = device.config{port = args.rxDev, rxQueues = 3, txQueues = 3}
	device.waitForLinks()
	local file = io.open("mf-lat.txt", "w")
	file:write("#flows rate meanLat stdevLat\n")
	setRate(txDev:getTxQueue(0), args.size, args.rate);
	for _,nflws in pairs({100,1000,10000,20000,30000,40000,50000,60000,63999}) do
		-- Heatup phase
		printf("heatup for %d flows - %d secs", nflws, args.upheat);
		local loadTask = mg.startTask("loadSlave", txDev:getTxQueue(0), rxDev, args.size, nflws, args.upheat)
		local timerTask = mg.startTask("timerSlave", txDev:getTxQueue(1), rxDev:getRxQueue(1), args.size, N_PROBE_FLOWS, args.upheat)
		local snt, rcv = loadTask:wait()
		mg.waitForTasks()
		printf("heatup results: %d sent, %f loss", snt, (snt-rcv)/snt);
		if (rcv < snt/100) then
			printf("unsuccessfull exiting");
			return	
		end
		mg.waitForTasks()
		-- Testing phase
		local loadTask = mg.startTask("loadSlave", txDev:getTxQueue(0), rxDev, args.size, nflws, args.timeout)
		local timerTask = mg.startTask("timerSlave", txDev:getTxQueue(1), rxDev:getRxQueue(1), args.size, N_PROBE_FLOWS, args.timeout)
		local packetsSent, packetsRecv = loadTask:wait()
		local latency, stdev = timerTask:wait()
		local loss = (packetsSent - packetsRecv)/packetsSent
		printf("total: %d flows, %f latency (+-%f)",
			nflws, latency, stdev);
		mg.waitForTasks()
		if (0 < loss) then
			printf("loss: %f --> queuing latency measurement is not representative", loss)
		else
			file:write(nflws .. " " .. args.rate .. " " .. latency .. " " .. stdev .. "\n")
		end
	end
end

local function fillUdpPacket(buf, len)
	buf:getUdpPacket():fill{
		ethSrc = queue,
		ethDst = DST_MAC,
		ip4Src = SRC_IP,
		ip4Dst = DST_IP,
		udpSrc = SRC_PORT,
		udpDst = DST_PORT,
		pktLength = len
	}
end

function loadSlave(queue, rxDev, size, flows, duration)
	local mempool = memory.createMemPool(function(buf)
		fillUdpPacket(buf, size)
	end)
	local bufs = mempool:bufArray()
	local counter = 0
	local finished = timer:new(duration)
	local fileTxCtr = stats:newDevTxCounter("txpkts", queue, "CSV", "txpkts.csv")
	local fileRxCtr = stats:newDevRxCounter("rxpkts", rxDev, "CSV", "rxpkts.csv")
	local txCtr = stats:newDevTxCounter(flows .. " tx", queue, "nil")
	local rxCtr = stats:newDevRxCounter(flows .. " rx", rxDev, "plain")
	local baseIP = parseIPAddress(SRC_IP_BASE)
	local baseSRCP = SRC_PORT
	local baseDSTP = DST_PORT
	while finished:running() and mg.running() do
		bufs:alloc(size)
		for i, buf in ipairs(bufs) do
			local pkt = buf:getUdpPacket()
			-- pkt.ip4.src:set(baseIP + counter)
			pkt.ip4.src:set(baseIP)
			-- pkt.udp.src = (baseSRCP + counter)
			pkt.udp.dst = (baseDSTP + counter)
			counter = incAndWrap(counter, flows)
		end
		-- UDP checksums are optional, so using just IPv4 checksums would be sufficient here
		bufs:offloadUdpChecksums()
		queue:send(bufs)
		txCtr:update()
		fileTxCtr:update()
		rxCtr:update()
		fileRxCtr:update()
	end
	txCtr:finalize()
	fileTxCtr:finalize()
	rxCtr:finalize()
	fileRxCtr:finalize()
	return txCtr.total, rxCtr.total
end

function timerSlave(txQueue, rxQueue, size, nflows, duration)
	if size < 84 then
		log:warn("Packet size %d is smaller than minimum timestamp size 84. Timestamped packets will be larger than load packets.", size)
		size = 84
	end
	local finished = timer:new(duration)
	local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
	local hist = hist:new()
	local counter = 0
	local rateLimit = timer:new(2.1/nflows)
	local baseIP = parseIPAddress(SRC_IP_BASE)
	local baseSRCP = START_PROBE_PORT
	while finished:running() and mg.running() do
		hist:update(timestamper:measureLatency(size, function(buf)
			fillUdpPacket(buf, size)
			local pkt = buf:getUdpPacket()
			-- pkt.ip4.src:set(baseIP + counter)
			pkt.ip4.src:set(baseIP)
			pkt.udp.src = (baseSRCP + counter)
			counter = incAndWrap(counter, nflows)
		end))
		rateLimit:wait()
		rateLimit:reset()
	end
	-- print the latency stats after all the other stuff
	mg.sleepMillis(300)
	hist:print()
	hist:save("latency-histogram.csv")
	return hist:median(), hist:standardDeviation()
end

