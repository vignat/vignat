-- Throughput Test (somewhat close to RFC2544)
-- as defined by https://www.ietf.org/rfc/rfc2544.txt
--  I guess the script is outdated and does not work anymore.
--  kept just in case

package.path = package.path ..";?.lua;test/?.lua;app/?.lua;../?.lua"

require "Pktgen";

-- this file does not exists.
dofile "$HOME/pktgenparams.lua" -- defines numFlows and resultFile

print(string.format("numFlows is %d\n",numFlows));

-- define packet sizes to test
-- local pkt_sizes		= { 64, 128, 256, 512, 1024, 1280, 1518 };
local pkt_sizes		= { 64};

-- Time in seconds to transmit for
local duration		= 3000;
local confirmDuration	= 80000;
local pauseTime		= 1000;

local strtprt_int = 1000;
local portStart = tostring(strtprt_int);
local portEnd = tostring(strtprt_int + numFlows);

local srcUDPPort = "1234";

-- define the ports in use
local recvport		= "0";
local sendport		= "1";

-- ip addresses to use
local dstip		= "192.168.2.10";
local srcip		= "192.168.3.5";
local netmask		= "/24";

local recvport_dst_mac = "00:1E:67:92:29:6C"
local sendport_dst_mac = "00:1E:67:92:29:6D"

local initialRate	= 50 ;

local function setupTraffic()
	pktgen.set_ipaddr(sendport, "dst", dstip);
	pktgen.set_ipaddr(sendport, "src", srcip..netmask);
	pktgen.set_mac(sendport, sendport_dst_mac);

	pktgen.set_ipaddr(recvport, "dst", srcip);
	pktgen.set_ipaddr(recvport, "src", dstip..netmask);
	pktgen.set_mac(recvport, recvport_dst_mac);

	pktgen.set_proto(sendport..","..recvport, "udp");
	-- set Pktgen to send continuous stream of traffic
	pktgen.set(sendport, "count", 0);

	pktgen.dst_port(sendport, "start", portStart);
	pktgen.dst_port(sendport, "inc", "1");
	pktgen.dst_port(sendport, "min", portStart);
	pktgen.dst_port(sendport, "max", portEnd);

	pktgen.src_port(sendport, "start", srcUDPPort);
	pktgen.src_port(sendport, "inc", "0");
	pktgen.src_port(sendport, "min", srcUDPPort);
	pktgen.src_port(sendport, "max", srcUDPPort);

	pktgen.dst_ip(sendport, "start", dstip);
	pktgen.dst_ip(sendport, "inc", "0");
	pktgen.dst_ip(sendport, "min", dstip);
	pktgen.dst_ip(sendport, "max", dstip);

	pktgen.src_ip(sendport, "start", srcip);
	pktgen.src_ip(sendport, "inc", "0");
	pktgen.src_ip(sendport, "min", srcip);
	pktgen.src_ip(sendport, "max", srcip);

	pktgen.dst_mac(sendport, "start", sendport_dst_mac);
	pktgen.dst_mac(sendport, "inc", "0");
	pktgen.dst_mac(sendport, "min", sendport_dst_mac);
	pktgen.dst_mac(sendport, "max", sendport_dst_mac);

	pktgen.range(sendport, "on");
end

local function runTrial(pkt_size, rate, duration, count)
	local num_tx, num_rx, num_dropped;

	pktgen.clr();
	pktgen.set(sendport, "rate", rate);
	pktgen.set(sendport, "size", pkt_size);

	pktgen.start(sendport);
	print("Running trial " .. count .. ". % Rate: " .. rate .. ". Packet Size: " .. pkt_size .. ". Duration (mS):" .. duration);
	-- file:write("Running trial " .. count .. ". % Rate: " .. rate .. ". Packet Size: " .. pkt_size .. ". Duration (mS):" .. duration .. "\n");
	pktgen.delay(duration);
	pktgen.stop(sendport);

	pktgen.delay(pauseTime);

	statTx = pktgen.portStats(sendport, "port")[tonumber(sendport)];
	statRx = pktgen.portStats(recvport, "port")[tonumber(recvport)];
	num_tx = statTx.opackets;
	num_rx = statRx.ipackets;
	num_dropped = num_tx - num_rx;

	print("Tx: " .. num_tx .. ". Rx: " .. num_rx .. ". Dropped: " .. num_dropped);
	-- file:write("Tx: " .. num_tx .. ". Rx: " .. num_rx .. ". Dropped: " .. num_dropped .. "\n");
	file:write(pkt_size .. " " .. rate .. " " .. num_tx .. " " .. num_rx .. " " .. duration .. "\n");
	pktgen.delay(pauseTime);

	return num_dropped;
end

local function runThroughputTest(pkt_size)
	local num_dropped, max_rate, min_rate, trial_rate;

	max_rate = 100;
	min_rate = 1;
	trial_rate = initialRate;
	for count=1, 1, 1 --10, 1
	do		
		num_dropped = runTrial(pkt_size, trial_rate, duration, count);
		if num_dropped == 0
		then
			min_rate = trial_rate;
		else
			max_rate = trial_rate;
		end
		trial_rate = min_rate + ((max_rate - min_rate)/2);
	end

	-- Ensure we test confirmation run with the last succesfull zero-drop rate
	trial_rate = min_rate;

	-- confirm throughput rate for at least 60 seconds
	--[[
	num_dropped = runTrial(pkt_size, trial_rate, confirmDuration, "Confirmation");
	if num_dropped == 0
	then
		print("Max rate for packet size "  .. pkt_size .. "B is: " .. trial_rate);
		file:write("Max rate for packet size "  .. pkt_size .. "B is: " .. trial_rate .. "\n\n");
	else
		print("Max rate of " .. trial_rate .. "% could not be confirmed for 60 seconds as required by rfc2544.");
		file:write("Max rate of " .. trial_rate .. "% could not be confirmed for 60 seconds as required by rfc2544." .. "\n\n");
	end
]]--
end

function main()
	file = io.open(resultFile, "w");
	setupTraffic();
	for _,size in pairs(pkt_sizes)
	do
		runThroughputTest(size);
	end
	file:close();
end


main();
os.exit();
