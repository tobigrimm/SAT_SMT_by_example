#-*- coding: utf-8 -*-

# Python 2.7

from lxml import etree
from sets import Set
import sys, time, re, os, networkx, copy

def list_remove_if_present(l, item):
    if item in l:
        l.remove(item)

def remove_item_in_all_lists(list_of_lists, item):
    for l in list_of_lists:
	list_remove_if_present(l, item)

def f2(cliques):
    sorted_cliques=sorted(cliques, key=len, reverse=True)

    for c in sorted_cliques:
	print "* clique size", len(c)
        for i in copy.deepcopy(c):
            print i
	    # remove all i's in all cliques
            remove_item_in_all_lists(sorted_cliques, i)
	break

def mainmain():
    
    G=networkx.read_gpickle(sys.argv[1])
    all_cliques=list(networkx.algorithms.clique.find_cliques(G))

    cliques=filter(lambda x: len(x) > 5, all_cliques)

    for i in range(1000):
	sys.stderr.write('clique #'+str(i)+'\n')
	f2(cliques)

mainmain()

