#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import sys, re, networkx

VERTICES=500

def do_all():
    f=open(sys.argv[1],"r")

    G=networkx.Graph()

    while True:
        raw=f.readline()
        l=raw.rstrip ()
        if len(l)==0:
            break

        m=re.search('UndirectedEdge\[(.*), (.*)\]', l)
        if m!=None:
            v1=int(m.group(1))
            v2=int(m.group(2))
            G.add_node(v1)
            G.add_node(v2)
            G.add_edge(v1, v2)

    f.close()

    for cl in networkx.algorithms.clique.find_cliques(G):
        if len(cl)<6:
            continue
        print len(cl), cl

do_all()

