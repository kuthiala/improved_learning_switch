#!/usr/bin/env python

from copy import deepcopy
from webob import Response
from ryu.app.wsgi import ControllerBase, WSGIApplication, route
from ryu.base import app_manager
from ryu.controller import ofp_event
from ryu.controller.handler import MAIN_DISPATCHER, CONFIG_DISPATCHER
from ryu.controller.handler import set_ev_cls
from ryu.ofproto import ofproto_v1_3
from ryu.lib.packet import packet
from ryu.lib.packet import ethernet
from ryu.lib.packet import ether_types
from ryu.lib.packet import ipv4
from ryu.lib.packet import udp
from ryu.lib.packet import icmp
from ryu.lib.packet import arp
from ryu.ofproto import ether, inet
from ryu.ofproto.ofproto_v1_2 import OFPG_ANY
import re
import chardet
from ryu.controller import dpset
import json
import time
from datetime import datetime, timedelta
import threading
from threading import Timer


simple_switch_instance_name = 'simple_switch_api_app'
topo_dict = {}
topo_graph = {}
dpid_ports = {}
mac_to_port = {}
ip_to_mac = {}
mac_to_ip = {}
link_dict = {}
global_dict = { 
                'topo_dict' : topo_dict,
                'topo_graph' : topo_graph,
                'dpid_ports': dpid_ports,
                'mac_to_port': mac_to_port,
                'ip_to_mac': ip_to_mac,
                'mac_to_ip': mac_to_ip,
                'link_dict': link_dict
              }
REQUIREMENTS = {'misc': r'[\w\d_]+|all'}

class RepeatedTimer(object):
    def __init__(self, interval, function, *args, **kwargs):
        self._timer = None
        self.interval = interval
        self.function = function
        self.args = args
        self.kwargs = kwargs
        self.is_running = False
        self.start()

    def _run(self):
        self.is_running = False
        self.start()
        self.function(*self.args, **self.kwargs)

    def start(self):
        if not self.is_running:
            self._timer = Timer(self.interval, self._run)
            self._timer.start()
            self.is_running = True

    def stop(self):
        self._timer.cancel()
        self.is_running = False

class SimpleSwitchController(ControllerBase):

    def __init__(self, req, link, data, **config):
        super(SimpleSwitchController, self).__init__(req, link, data, **config)
        self.simple_switch_app = data[simple_switch_instance_name]

    @route('global_topo', '/topology/', methods=['GET'])
    def show_topo(self, req, **kwargs):
        print('Returning the global topology in JSON')
        body = json.dumps(topo_dict)
        return Response(content_type='application/json', body=body)

    @route('global_topo', '/phones/', methods=['GET'])
    def show_phones(self, req, **kwargs):
        print('Returning the phones in JSON')
        body = json.dumps(phone_ext_info)
        return Response(content_type='application/json', body=body)

    @route('global_topo', '/switches/', methods=['GET'])
    def show_switches(self, req, **kwargs):
        print('Returning the switches in JSON')
        body = json.dumps(dpid_ports)
        return Response(content_type='application/json', body=body)

    @route('misc', '/misc/{misc}', methods=['GET'], requirements=REQUIREMENTS)
    def misc(self, req, misc, **_kwargs):
        print('Returning {} in JSON'.format(misc))
        body = json.dumps(global_dict[misc])
        return Response(content_type='application/json', body=body)

    @route('favicon', '/favicon.ico', methods=['GET'])
    def favicon(self, req, **kwargs):
        return Response(content_type='image/png', body=open("www/favicon.png", "rb").read())

class VoIP_Capstone4(app_manager.RyuApp):
    OFP_VERSIONS = [ofproto_v1_3.OFP_VERSION]
    _CONTEXTS = {'wsgi': WSGIApplication}

    def __init__(self, *args, **kwargs):
        super(VoIP_Capstone4, self).__init__(*args, **kwargs)
        self.broadcast_mac = 'FF:FF:FF:FF:FF:FF'
        self.dpid_to_datapath = {}
        self.started_topo_discovery = False
        self.topo_discovery_port = 20000
        self.vip = '192.168.1.1'
        self.vmac = '00:00:00:10:01:11'
        self.topo_timer = 3
        self.switch_interconnection_ports = {}
        self.idle_timeout = 5
        self.hard_timeout = 5
        wsgi = kwargs['wsgi']
        wsgi.register(SimpleSwitchController,
                      {simple_switch_instance_name: self})
    def send_tracer_frames(self):
        for dpid, datapath in self.dpid_to_datapath.items():
            dpid = datapath.id
            parser = datapath.ofproto_parser
            if dpid in dpid_ports.keys():
                for out_port in dpid_ports[dpid].keys():
                    actions = [parser.OFPActionOutput(out_port)]
                    out = parser.OFPPacketOut(datapath=datapath,
                                            buffer_id=0xffffffff,
                                            in_port=0,
                                            actions=actions,
                                            data=self.create_tracer_frame(dpid, out_port, dpid_ports[dpid][out_port]['curr_speed']))
                    datapath.send_msg(out)
        for dpid in topo_dict.keys():
            for local_port in topo_dict[dpid].keys():
                if "TX_TIMESTAMP" in topo_dict[dpid][local_port].keys():
                    timestamp_since_last_hello = topo_dict[dpid][local_port]["TX_TIMESTAMP"]
                    time_since_last_hello = (datetime.now() -
                                             datetime.strptime(timestamp_since_last_hello,
                                                               "%Y-%m-%d %H:%M:%S.%f"
                                                              )).total_seconds()
                    if time_since_last_hello > 3 * self.topo_timer:
                        del topo_graph[dpid][topo_dict[dpid][local_port]["REMOTE_DPID"]]
                        del topo_dict[dpid][local_port]
                        link_dict[dpid][local_port][-1] = False
        for dpid in topo_dict.keys():
            if topo_dict[dpid] == {}:
                del topo_dict[dpid]
                del topo_graph[dpid]

    def add_flow(self, datapath, priority, match, actions, command=0, buffer_id=None, idle_timeout=0, hard_timeout=0, out_port=0, out_group=0, do_not_display=False):
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser

        inst = [parser.OFPInstructionActions(ofproto.OFPIT_APPLY_ACTIONS,
                                             actions)]
        if buffer_id:
            mod = parser.OFPFlowMod(datapath=datapath,
                                    buffer_id=buffer_id,
                                    priority=priority,
                                    command=command,
                                    idle_timeout=idle_timeout,
                                    hard_timeout=hard_timeout,
                                    out_port=out_port,
                                    out_group=out_group,
                                    match=match,
                                    instructions=inst)
        else:
            mod = parser.OFPFlowMod(datapath=datapath,
                                    priority=priority,
                                    command=command,
                                    idle_timeout=idle_timeout,
                                    hard_timeout=hard_timeout,
                                    out_port=out_port,
                                    out_group=out_group,
                                    match=match,
                                    instructions=inst)
        if not do_not_display:
            self.logger.info("Adding flow on {} -> Match {} Actions: {}".format(datapath.id, match.items.im_self, actions))
        datapath.send_msg(mod)

    def pretty_print(self, dictionary):
        self.logger.info(json.dumps(dictionary, indent=4, sort_keys=True))

    def create_tracer_frame(self, dpid, outport, outport_speed):
        payload_dict = {"EGRESS_DPID" : dpid,
                        "OUT_PORT" : outport,
                        "BANDWIDTH" : outport_speed,
                        "TX_TIMESTAMP" : datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f")
                       }
        ethernet_header_tracer = ethernet.ethernet(dst=self.vmac,
                                                   src=self.vmac,
                                                   ethertype=2048)
        tracer_packet = packet.Packet()
        tracer_packet.add_protocol(ethernet_header_tracer)
        tracer_packet.add_protocol(ipv4.ipv4(dst=self.vip,
                                             src=self.vip,
                                             proto=inet.IPPROTO_UDP))
        tracer_packet.add_protocol(udp.udp(dst_port=self.topo_discovery_port, src_port=self.topo_discovery_port))
        tracer_packet.add_protocol(payload_dict)
        return tracer_packet

    def flood_network_edge(self, in_dpid, in_port, data):
        for dpid in dpid_ports.keys():
            parser = self.dpid_to_datapath[dpid].ofproto_parser
            ofproto = self.dpid_to_datapath[dpid].ofproto
            all_ports_set = set(dpid_ports[dpid].keys())
            all_internal_ports_set =  set()
            if dpid in link_dict.keys():
                all_internal_ports_set = set(link_dict[dpid].keys())
            all_edge_ports = list(all_ports_set - all_internal_ports_set)
            if in_dpid == dpid:
                all_edge_ports.remove(in_port)
            for edge_port in all_edge_ports:
                actions = [parser.OFPActionOutput(edge_port)]
                out = parser.OFPPacketOut(datapath=self.dpid_to_datapath[dpid],
                                    buffer_id=ofproto.OFP_NO_BUFFER,
                                    in_port=ofproto.OFPP_CONTROLLER,
                                    actions=actions,
                                    data=data)
                self.dpid_to_datapath[dpid].send_msg(out)
        return

    def dijkstras(self, source, goal, graph):
        # keeps track of paths to node. Node: (cost, [PATH])
        cost_path = {n: (float("inf"), None) for n in graph}
        cost_path[source] = (0, [source])
        visited = set()

        # while there are still nodes to be visited
        while len(visited) != len(graph):
            # find the lowest cost unvisited node
            min_node = None
            min_val = float("inf")
            for n in cost_path:
                if n not in visited:
                    if cost_path[n][0] < min_val:
                        min_node = n

            # goal check
            if min_node == goal:
                return cost_path[min_node]

            # add to visited, update neighbors if a better path exisits
            visited.add(min_node)
            for n in graph[min_node]:
                if n not in visited:
                    if cost_path[min_node][0] + graph[min_node][n] < cost_path[n][0]:
                        cost_path[n] = (cost_path[min_node][0] + graph[min_node][n], cost_path[min_node][1] + [n])
        return None

    def install_topo_flows(self, source, goal, pkt, bidirectional=True):
        dijkstra_tup = (self.dijkstras(source, goal, topo_graph))
        least_latency_path = dijkstra_tup[-1]
        reverse_latency_path = deepcopy(least_latency_path)
        reverse_latency_path.reverse()
        eth = pkt.get_protocols(ethernet.ethernet)[0]
        if eth.ethertype == ether.ETH_TYPE_IP:
            ip_pkt = pkt.get_protocol(ipv4.ipv4)
            sip = ip_pkt.src
            dip = ip_pkt.dst
            for path_list, src_ip, dst_ip in zip([least_latency_path,reverse_latency_path],[sip,dip],[dip,sip]): 
                for ind,switch in enumerate(path_list[:-1]):
                    for local_port in topo_dict[switch].keys():
                        if "REMOTE_DPID" in topo_dict[switch][local_port].keys():
                            if topo_dict[switch][local_port]["REMOTE_DPID"] == path_list[ind+1]:
                                out_port = local_port
                                datapath = self.dpid_to_datapath[switch]
                                ofproto = datapath.ofproto
                                parser = datapath.ofproto_parser
                                match = parser.OFPMatch(eth_type=2048 ,ip_proto=ip_pkt.proto ,ipv4_dst=dst_ip, ipv4_src=src_ip)
                                actions = [parser.OFPActionOutput(out_port)]
                                self.add_flow(datapath, 10000, match, actions, idle_timeout=self.idle_timeout)
                                break
                else:
                    switch = path_list[-1]
                    for local_port in topo_dict[switch].keys():
                        if "DEVICE" in topo_dict[switch][local_port].keys():
                            if topo_dict[switch][local_port]["DEVICE"]["IP"] == dst_ip:
                                out_port = local_port
                                datapath = self.dpid_to_datapath[switch]
                                ofproto = datapath.ofproto
                                parser = datapath.ofproto_parser
                                match = parser.OFPMatch(eth_type=2048 ,ip_proto=ip_pkt.proto ,ipv4_dst=dst_ip, ipv4_src=src_ip)
                                actions = [parser.OFPActionOutput(out_port)]
                                self.add_flow(datapath, 10000, match, actions, idle_timeout=self.idle_timeout)
                if not bidirectional:
                    break
        return

    def remove_stale_topo_info(self, dpid, sip, src, in_port):
        for switch in topo_dict.keys():
            for local_port in topo_dict[switch].keys():
                if "DEVICE" in topo_dict[switch][local_port].keys():
                    if sip == topo_dict[switch][local_port]["DEVICE"]["IP"] and topo_dict[switch][local_port]["DEVICE"]["TYPE"] != "Phone":
                        del topo_dict[switch][local_port]
                        return            
    
    @set_ev_cls(ofp_event.EventOFPPortDescStatsReply, MAIN_DISPATCHER)
    def port_desc_handler(self, ev):
        msg = ev.msg
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        ports = []
        dpid = datapath.id
        dpid_ports.setdefault(dpid, {})
        for port_stat in ev.msg.body:
            ports.append('port_no=%d hw_addr=%s name=%s config=0x%08x '
                         'state=0x%08x curr=0x%08x advertised=0x%08x '
                         'supported=0x%08x peer=0x%08x curr_speed=%d '
                         'max_speed=%d' %
                         (port_stat.port_no, port_stat.hw_addr,
                          port_stat.name, port_stat.config,
                          port_stat.state, port_stat.curr, port_stat.advertised,
                          port_stat.supported, port_stat.peer, port_stat.curr_speed,
                          port_stat.max_speed
                         )
                        )
            dpid_ports[dpid][int(port_stat.port_no)] = dict(
                hw_addr=port_stat.hw_addr,
                name=port_stat.name,
                curr_speed=port_stat.curr_speed
            )
        self.logger.debug('OFPPortDescStatsReply received: %s', ports)


    @set_ev_cls(ofp_event.EventOFPSwitchFeatures, CONFIG_DISPATCHER)
    def switch_features_handler(self, ev):
        msg = ev.msg
        datapath = ev.msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        dpid = datapath.id

        # install table-miss flow entry
        #
        # We specify NO BUFFER to max_len of the output action due to
        # OVS bug. At this moment, if we specify a lesser number, e.g.,
        # 128, OVS will send Packet-In with invalid buffer_id and
        # truncated packet data. In that case, we cannot output packets
        # correctly.  The bug has been fixed in OVS v2.1.0.

        # clear all flows
        self.add_flow(datapath, 0, parser.OFPMatch(), 
        [], command = ofproto.OFPFC_DELETE, 
        out_port = ofproto.OFPP_ANY, out_group = OFPG_ANY)

        match = parser.OFPMatch()
        actions = [parser.OFPActionOutput(ofproto.OFPP_CONTROLLER,
                                          ofproto.OFPCML_NO_BUFFER)]
        self.add_flow(datapath, 10, match, actions)
        # Drop IPv6 packets
        match = parser.OFPMatch(eth_type=0x86dd)
        self.add_flow(datapath, 32000, match, [])
        # Request port information from the switch
        req = parser.OFPPortDescStatsRequest(datapath, 0, ofproto.OFPP_ANY)
        datapath.send_msg(req)

        self.logger.info("Registered Switch: {}".format(datapath.id))
        self.send_tracer_frames()

        self.dpid_to_datapath[dpid] = datapath
        if not self.started_topo_discovery:
            RepeatedTimer(self.topo_timer, self.send_tracer_frames)
            self.started_topo_discovery = True

    @set_ev_cls(ofp_event.EventOFPPacketIn, MAIN_DISPATCHER)
    def _packet_in_handler(self, ev):
        # If you hit this you might want to increase
        # the "miss_send_length" of your switch
        if ev.msg.msg_len < ev.msg.total_len:
            self.logger.debug("packet truncated: only %s of %s bytes",
                              ev.msg.msg_len, ev.msg.total_len)
        msg = ev.msg
        datapath = msg.datapath
        ofproto = datapath.ofproto
        parser = datapath.ofproto_parser
        in_port = msg.match['in_port']

        pkt = packet.Packet(msg.data)
        eth = pkt.get_protocols(ethernet.ethernet)[0]

        if eth.ethertype == ether_types.ETH_TYPE_LLDP:
            # ignore lldp packet
            return
        dst = eth.dst
        src = eth.src

        dpid = datapath.id
        self.dpid_to_datapath[dpid] = datapath
        mac_to_port.setdefault(dpid, {})

        # self.logger.info("packet in %s %s %s %s", dpid, src, dst, in_port)

        # learn a mac address to avoid FLOOD next time. Don't learn the vmac
        if dst != self.vmac and src != self.vmac:
            mac_to_port[dpid][src] = in_port

        for switch in mac_to_port.keys():
            if dst in mac_to_port[switch].keys():
                out_port = mac_to_port[switch][dst]
                actions = [parser.OFPActionOutput(out_port)]
                data = msg.data
                out = parser.OFPPacketOut(datapath=self.dpid_to_datapath[switch],
                                        buffer_id=ofproto.OFP_NO_BUFFER,
                                        in_port=ofproto.OFPP_CONTROLLER,
                                        actions=actions,
                                        data=data)
                # print(datapath.id, in_port, actions, data)
                self.dpid_to_datapath[switch].send_msg(out)
                #  Install low priority L2 flows in the topo.
                self.install_topo_flows(dpid, switch, pkt, bidirectional=True)
                break
        # handle unknown unicast and broadcast, flood the network edges.
        # flood only if it's not a topology discovery packet.
        else:
            # don't flood the network edge if the packet is a tracer packet
            try:
                if  eth.ethertype == ether.ETH_TYPE_IP:
                    if  pkt.get_protocols(ipv4.ipv4)[0].proto != inet.IPPROTO_UDP or \
                        pkt.get_protocol(ipv4.ipv4).dst != self.vip or \
                        pkt.get_protocol(ipv4.ipv4).src != self.vip and \
                        pkt.get_protocol(ipv4.ipv4).dst != self.vip:
                        self.flood_network_edge(dpid, in_port, msg.data)
                elif eth.ethertype == ether.ETH_TYPE_ARP:
                    if  pkt.get_protocols(arp.arp)[0].dst_ip != self.vip or \
                        pkt.get_protocols(arp.arp)[0].opcode != 1:
                        self.flood_network_edge(dpid, in_port, msg.data)
                else:
                    self.flood_network_edge(dpid, in_port, msg.data)
            except:
                self.flood_network_edge(dpid, in_port, msg.data)
        
        # Handle arp requests to the SIP server.
        if eth.ethertype == ether_types.ETH_TYPE_ARP:
            arp_header = pkt.get_protocols(arp.arp)[0]
            mac_to_ip[src] = arp_header.src_ip
            ip_to_mac[arp_header.src_ip] = src
            if arp_header.dst_ip == self.vip and arp_header.opcode == 1:
                self.logger.info('Rx ARP-REQ for PBX. Fabricating an ARP reply.')
                ethernet_header_to_send = ethernet.ethernet(dst=eth.src,
                                                            src=self.vmac,
                                                            ethertype=2054)
                arp_header_to_send = arp.arp(hwtype=1,
                                             proto=0x0800,
                                             hlen=6,
                                             plen=4,
                                             opcode=2,
                                             src_mac=self.vmac,
                                             src_ip=self.vip,
                                             dst_mac=eth.src,
                                             dst_ip=arp_header.src_ip)

                packet_to_send = packet.Packet()
                packet_to_send.add_protocol(ethernet_header_to_send)
                packet_to_send.add_protocol(arp_header_to_send)
                packet_to_send.serialize()
                data = packet_to_send.data
                actions = [parser.OFPActionOutput(in_port)]
                out = parser.OFPPacketOut(datapath=datapath,
                                          buffer_id=0xffffffff,
                                          in_port=ofproto.OFPP_ANY,
                                          actions=actions,
                                          data=data)
                # print(datapath.id, in_port, actions, data)
                datapath.send_msg(out)
                return

        elif eth.ethertype == ether.ETH_TYPE_IP:
            ip_pkt = pkt.get_protocol(ipv4.ipv4)
            sip = ip_pkt.src
            dip = ip_pkt.dst
            iphdr = pkt.get_protocols(ipv4.ipv4)[0]
            if sip != self.vip:
                self.remove_stale_topo_info(dpid, sip, src, in_port)
                topo_dict.setdefault(dpid, {})
                topo_dict[dpid].setdefault(in_port, {})
                topo_dict[dpid][in_port].setdefault("DEVICE", {})
                topo_dict[dpid][in_port]["DEVICE"] = {"IP": sip, "MAC": src, "TYPE": "unknown"}
            if iphdr.proto == inet.IPPROTO_ICMP and dip == self.vip:
                icmp_pkt = pkt.get_protocol(icmp.icmp)
                print "Got ICMP for the SIP server"
                self.logger.info("Src IP: {}, Dst IP: {}".format(sip, dip))
                pakt = packet.Packet()
                pakt.add_protocol(ethernet.ethernet(dst = src,
                                                    src = self.vmac,
                                                    ethertype = ether.ETH_TYPE_IP))
                pakt.add_protocol(ipv4.ipv4(dst=sip,
                                            src = self.vip,
                                            proto = ip_pkt.proto))
                pakt.add_protocol(icmp.icmp(type_ = icmp.ICMP_ECHO_REPLY,
                                            code = icmp.ICMP_ECHO_REPLY_CODE,
                                            csum = 0,
                                            data = icmp_pkt.data))
                pakt.serialize()
                actions = [parser.OFPActionOutput(in_port)]
                out = parser.OFPPacketOut(datapath=datapath,
                                            in_port=ofproto.OFPP_ANY,
                                            data=pakt.data,
                                            actions=actions,
                                            buffer_id=0xffffffff)
                # print(datapath.id, in_port, actions, data)
                datapath.send_msg(out)

            if iphdr.proto == inet.IPPROTO_UDP and dip == self.vip and sip == self.vip:
                udp_pkt = pkt.get_protocol(udp.udp)
                sport = udp_pkt.src_port
                dport = udp_pkt.dst_port
                if (sport == self.topo_discovery_port) and (dport == self.topo_discovery_port):
                    match_bcast = parser.OFPMatch(eth_dst=self.broadcast_mac, in_port=in_port)
                    self.add_flow(datapath, 32000, match_bcast, [], idle_timeout=self.idle_timeout, do_not_display=True)
                    tracer_str = pkt.protocols[-1].replace("'", "\"")
                    tracer_dict = json.loads(tracer_str)
                    topo_dict.setdefault(dpid, {})
                    topo_dict[dpid][in_port] = {
                        "LINK_LATENCY": (datetime.now() - 
                                        datetime.strptime(tracer_dict["TX_TIMESTAMP"], 
                                                          "%Y-%m-%d %H:%M:%S.%f")).total_seconds(),
                        "RX_TIMESTAMP": datetime.now().strftime("%Y-%m-%d %H:%M:%S.%f"),
                        "REMOTE_DPID" : tracer_dict["EGRESS_DPID"], 
                        "REMOTE_PORT": tracer_dict["OUT_PORT"], 
                        "REMOTE_BANDWIDTH" : tracer_dict["BANDWIDTH"],
                        "TX_TIMESTAMP": tracer_dict["TX_TIMESTAMP"]
                        }
                    # build the graph for djikstra
                    topo_graph.setdefault(dpid, {})
                    topo_graph[dpid][topo_dict[dpid][in_port]["REMOTE_DPID"]] = topo_dict[dpid][in_port]["LINK_LATENCY"]
                    # build the link up/down database
                    link_dict.setdefault(dpid, {})
                    link_dict[dpid][in_port] = [tracer_dict["EGRESS_DPID"], tracer_dict["OUT_PORT"], True]             
                return
