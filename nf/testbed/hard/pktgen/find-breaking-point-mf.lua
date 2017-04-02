-- Run search to find the point at which the middle box start
-- loosing 1% of the packets

package.path = package.path ..";?.lua;test/?.lua;app/?.lua;../?.lua"

require "Pktgen";

-- define packet sizes to test
local pkt_sizes		= { 64 };

local flows_nums = { 1000, 10000, 20000, 30000, 40000, 50000, 55000, 60000, 62000, 63000, 63500, 64000, 64500, 65000, 65535 };

-- Time in seconds to transmit for
local duration		= 40000;
local pauseTime		= 2000;

-- the part to start from
local strtprt_int = 0;


local num_bin_steps = 7;

local srcUDPPort = "1234";

-- define the ports in use
local recvport		= "0";
local sendport		= "1";

-- ip addresses to use
local dstip		= "192.168.4.10";
local srcip		= "192.168.6.5";
local netmask		= "/24";

local recvport_dst_mac = "90:e2:ba:55:14:10"
local sendport_dst_mac = "90:e2:ba:55:14:11"

local initialRate	= 50 ;

local function setupTraffic(numFlows)
	local portStart = tostring(strtprt_int);
	local portEnd = tostring(strtprt_int + (numFlows - 1)); -- beware of overflows!
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

local function runTrial(numFlows, pkt_size, rate, duration, count)
	local num_tx, num_rx, num_dropped;

	pktgen.clr();
	pktgen.set(sendport, "rate", rate);
	pktgen.set(sendport, "size", pkt_size);

	pktgen.start(sendport);
	print("#" .. count .. ", |pkt|=" .. pkt_size .. ", rate=" .. rate .. ", #flows=" .. numFlows .. ", duration=" .. duration .. "ms");
	pktgen.delay(duration);
	pktgen.stop(sendport);
	

	pktgen.delay(pauseTime);

	statTx = pktgen.portStats(sendport, "port")[tonumber(sendport)];
	statRx = pktgen.portStats(recvport, "port")[tonumber(recvport)];
	num_tx = statTx.opackets;
	num_rx = statRx.ipackets;
	num_dropped = (num_tx - num_rx)/num_tx;

	print("TX=" .. num_tx .. " / RX=" .. num_rx .. " -> Drop: " .. num_dropped);
	pktgen.delay(pauseTime);

	return num_dropped, num_tx;
end

local function runThroughputTest(numFlows, pkt_size)
	local num_dropped, max_rate, min_rate,
 	      trial_rate, abs_min_rate, abs_max_rate, num_tx;
	local reg50_step, reg100_step;
	local steps_to50, steps_to100;

	abs_max_rate = 100;
	abs_min_rate = 1;
	max_rate = abs_max_rate;
	min_rate = abs_min_rate;
	tot_count = 0;

	-- Start with 100% then with 1%, the most common cases, to speed things up
	trial_rate = 100
	num_dropped, num_tx = runTrial(numFlows, pkt_size, trial_rate, duration, tot_count);
	if num_dropped >= 0.01
	then
		tot_count = tot_count + 1
		trial_rate = 1
		num_dropped, num_tx = runTrial(numFlows, pkt_size, trial_rate, duration, tot_count);
		if num_dropped < 0.01
		then
			trial_rate = initialRate;
			for count=1, num_bin_steps, 1
			do
				num_dropped, num_tx = runTrial(numFlows, pkt_size, trial_rate, duration, tot_count);
				tot_count = tot_count + 1;
				if num_dropped < 0.01
				then
					min_rate = trial_rate;
				else
					max_rate = trial_rate;
				end
				trial_rate = min_rate + ((max_rate - min_rate)/2);
			end
		end
	end
	num_tx_per_sec = math.floor(num_tx / (duration / 1000));
	file:write(numFlows .. " " .. pkt_size .. " " .. trial_rate .. " " .. num_tx .. " " .. num_tx_per_sec .. "\n");
end

function main()
	file = io.open("multi-flows.txt", "w");
	file:write("#flows pkt_size rate #pkt #pkt/sec\n");

	runTrial(10000, 64, 1, 100000, "heatup");
	for _,numFlows in pairs(flows_nums)
	do
		setupTraffic(numFlows);
		for _,size in pairs(pkt_sizes)
		do
			runThroughputTest(numFlows, size);
		end
	end
	file:close();
end


main();
os.exit();
