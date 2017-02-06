-- Prepare PktGen to run experiments in request-response fashion

package.path = package.path ..";?.lua;test/?.lua;app/?.lua;../?.lua"

require "Pktgen";

local strtprt_int = 0;

local srcUDPPort = "1234";

-- define the ports in use
local sendport		= "0";

-- ip addresses to use
local dstip		= "192.168.200.10";
local srcip		= "192.168.2.10";
local netmask		= "/24";

local sendport_dst_mac = "00:1E:67:92:29:6C"

local function setupTraffic(numFlows)
	local portStart = tostring(strtprt_int);
	local portEnd = tostring(strtprt_int + (numFlows - 1));
	pktgen.set_ipaddr(sendport, "dst", dstip);
	pktgen.set_ipaddr(sendport, "src", srcip..netmask);
	pktgen.set_mac(sendport, sendport_dst_mac);

	pktgen.set_proto("all", "udp");
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
