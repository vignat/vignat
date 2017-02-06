-- Prepare PktGen for performance experiments, that will be requested via
-- the port 22022
-- Unused (for now?)

package.path = package.path ..";?.lua;test/?.lua;app/?.lua;../?.lua"

require "Pktgen";

-- define packet sizes to test
-- local pkt_sizes		= { 64, 128, 256, 512, 1024, 1280, 1518 };
-- Time in seconds to transmit for
local duration		= 30000;
--local confirmDuration	= 80000;
local pauseTime		= 2000;

local strtprt_int = 1000;


local num_reg_steps = 10;
local num_bin_steps = 5;

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
end

setupTraffic();
