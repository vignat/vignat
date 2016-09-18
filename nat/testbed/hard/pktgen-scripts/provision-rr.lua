-- RFC2544 Throughput Test
-- as defined by https://www.ietf.org/rfc/rfc2544.txt

package.path = package.path ..";?.lua;test/?.lua;app/?.lua;../?.lua"

require "Pktgen";

-- define packet sizes to test
-- local pkt_sizes		= { 64, 128, 256, 512, 1024, 1280, 1518 };
local pkt_sizes		= { 64};--, 128};

local flows_nums = {1, 7500, 20000}; --{ 1, 100, 1000, 7500, 20000, 30000 };

-- Time in seconds to transmit for
local duration		= 40000;
--local confirmDuration	= 80000;
local pauseTime		= 2000;

local strtprt_int = 1000;


local num_reg_steps = 10;
local num_bin_steps = 5;

local srcUDPPort = "1234";

-- define the ports in use
local sendport		= "0";

-- ip addresses to use
local dstip		= "192.168.200.10";
local srcip		= "192.168.2.10";
local netmask		= "/24";

--local recvport_dst_mac = "00:1E:67:92:29:6C"
local sendport_dst_mac = "00:1E:67:92:29:6C"

local initialRate	= 50 ;

local function setupTraffic(numFlows)
	local portStart = tostring(strtprt_int);
	local portEnd = tostring(strtprt_int + numFlows);
	pktgen.set_ipaddr(sendport, "dst", dstip);
	pktgen.set_ipaddr(sendport, "src", srcip..netmask);
	pktgen.set_mac(sendport, sendport_dst_mac);

	--pktgen.set_ipaddr(recvport, "dst", srcip);
	--pktgen.set_ipaddr(recvport, "src", dstip..netmask);
	--pktgen.set_mac(recvport, recvport_dst_mac);

	pktgen.set_proto("all", "tcp");
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

setupTraffic(50000);

pktgen.set(sendport, "rate", 1);
