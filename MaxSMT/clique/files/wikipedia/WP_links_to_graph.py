#-*- coding: utf-8 -*-

# Python 2.7

# may require up to 32GB of RAM to process English Wikipedia'2015

from lxml import etree
from sets import Set
import sys, time, re, os, networkx, copy

def wikipedia_main_namespace(title):
    if title.startswith ("Wikipedia:"):
        return False
    if title.startswith ("Wikipedia talk:"):
        return False
    if title.startswith ("User:"):
        return False
    if title.startswith ("User talk:"):
        return False
    if title.startswith ("Category:"):
        return False
    if title.startswith ("Category talk:"):
        return False
    if title.startswith ("Talk:"):
        return False
    if title.startswith ("File:"):
        return False
    if title.startswith ("File talk:"):
        return False
    if title.startswith ("Template:"):
        return False
    if title.startswith ("Template talk:"):
        return False
    if title.startswith ("Portal:"):
        return False
    if title.startswith ("Special:"):
        return False
    if title.startswith (":"):
        return False
    return True

def capitalize(line):
    if len(line)==0:
        return line
    if len(line)==1:
        return line.upper()
    return line[0].upper() + line[1:]

def process_redirects (fname):
    redirects={}
    with open(fname,'r') as file:
        for line in file:
            m = re.search('REDIRECT \| ([^\|]*) \| ([^\|\n]*)', line)
            if m!=None:
		rfrom=m.group(1)
		rto=m.group(2)
		if wikipedia_main_namespace(rfrom) and wikipedia_main_namespace(rto):
		    redirects[capitalize(rfrom)]=capitalize(rto)
            else:
                #print "line unparsed",line
                pass
    return redirects

def process_links (fname, redirects):
    links={}
    lines_read=0
    
    with open(fname,'r') as file:
        for line in file:
            lines_read=lines_read+1
	    if (lines_read % 100000)==0:
	        print "process_links(), lines_read=", lines_read
            m = re.search('LINK \| ([^\|]*) \| ([^\|\n]*)', line)
            if m!=None:
	        lfrom=m.group(1)
		lto=m.group(2)
		if lfrom.startswith('{{'): # skip templates
	            continue
		lfrom_cap=capitalize(lfrom)
		if wikipedia_main_namespace(lfrom):
		    if lfrom_cap not in links:
                        links[lfrom_cap]=Set()
		    # fix redirects
		    if lto in redirects:
	                lto=redirects[lto]
                    if wikipedia_main_namespace(lto):
		        links[lfrom_cap].add(capitalize(lto))

            else:
                #print "line unparsed",line
                pass
    return links

# command line: redirects, links, pickle
def mainmain():
    redirects=process_redirects(sys.argv[1])
    print "redirects", len(redirects)
    sys.stderr.write(sys.argv[1]+" processed\n")

    links=process_links(sys.argv[2], redirects)
    links_t=len(links)
    print "links", links_t
    sys.stderr.write(sys.argv[2]+" processed\n")

    G=networkx.Graph()

    articles_processed=0

    for article in links:
	articles_processed=articles_processed+1
	if (articles_processed % 100000)==0:
	    sys.stdout.write('links processed=' + str(articles_processed) + '/' + str(links_t) + ' (%'+str(articles_processed*100/links_t)+')\n')
        if len(links[article])<6:
            continue
        G.add_node(article)
        for l in links[article]:
	    if (l in links) and (article in links[l]): # back link is also present
                G.add_node(l)
                G.add_edge(article, l)

    networkx.write_gpickle(G,sys.argv[3])

mainmain()

