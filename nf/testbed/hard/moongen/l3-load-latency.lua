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
local SRC_PORT		= 234
local DST_PORT		= 319

function configure(parser)
	parser:description("Generates UDP traffic and measure latencies. Edit the source to modify constants like IPs.")
	parser:argument("txDev", "Device to transmit from."):convert(tonumber)
	parser:argument("rxDev", "Device to receive from."):convert(tonumber)
	parser:option("-r --rate", "Transmit rate in Mbit/s."):default(10000):convert(tonumber)
	parser:option("-f --flows", "Number of flows (randomized source IP)."):default(4):convert(tonumber)
	parser:option("-s --size", "Packet size."):default(60):convert(tonumber)
	parser:option("-h --heatup", "Heatup time before beginning of latency measurement"):default(2):convert(tonumber)
	parser:option("-t --timeout", "Time to run the test"):default(0):convert(tonumber)
end

function master(args)
	txDev = device.config{port = args.txDev, rxQueues = 3, txQueues = 3}
	rxDev = device.config{port = args.rxDev, rxQueues = 3, txQueues = 3}
	device.waitForLinks()
	-- max 1kpps timestamping traffic timestamping
	-- rate will be somewhat off for high-latency links at low rates
	if args.rate > 0 then
		txDev:getTxQueue(0):setRate(args.rate - (args.size + 4) * 8 / 1000)
	end
	mg.startTask("loadSlave", txDev:getTxQueue(0), rxDev, args.size, args.flows)
	mg.startTask("timerSlave", txDev:getTxQueue(1), rxDev:getRxQueue(1), args.size, args.flows, args.heatup)
	if (args.timeout < 1) then
		mg.waitForTasks()
	else
		mg.sleepMicrosIdle((args.timeout + 1)*1000000)
		mg.stop()
		mg.waitForTasks()
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

function loadSlave(queue, rxDev, size, flows)
	local mempool = memory.createMemPool(function(buf)
		fillUdpPacket(buf, size)
	end)
	local bufs = mempool:bufArray()
	local counter = 0
	local fileTxCtr = stats:newDevTxCounter("txpkts", queue, "CSV", "txpkts.csv")
	local fileRxCtr = stats:newDevRxCounter("rxpkts", rxDev, "CSV", "rxpkts.csv")
	local txCtr = stats:newDevTxCounter(flows .. " tx", queue, "plain")
	local rxCtr = stats:newDevRxCounter(flows .. " rx", rxDev, "plain")
	local baseIP = parseIPAddress(SRC_IP_BASE)
	local baseSRCP = SRC_PORT
	local baseDSTP = DST_PORT
	while mg.running() do
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
end

function timerSlave(txQueue, rxQueue, size, flows, heatup)
	if size < 84 then
		log:warn("Packet size %d is smaller than minimum timestamp size 84. Timestamped packets will be larger than load packets.", size)
		size = 84
	end
	local timestamper = ts:newUdpTimestamper(txQueue, rxQueue)
	local hist = hist:new()
	mg.sleepMillis(heatup) -- ensure that the load task is running
	local counter = 0
	local rateLimit = timer:new(0.001)
	local baseIP = parseIPAddress(SRC_IP_BASE)
	local baseSRCP = SRC_PORT
	while mg.running() do
		hist:update(timestamper:measureLatency(size, function(buf)
			fillUdpPacket(buf, size)
			local pkt = buf:getUdpPacket()
			-- pkt.ip4.src:set(baseIP + counter)
			pkt.ip4.src:set(baseIP)
			pkt.udp.src = (baseSRCP + counter)
			counter = incAndWrap(counter, flows)
		end))
		rateLimit:wait()
		rateLimit:reset()
	end
	-- print the latency stats after all the other stuff
	mg.sleepMillis(300)
	hist:print()
	hist:save("latency-histogram.csv")
end

