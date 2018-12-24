#-*- coding: utf-8 -*-

import re, os, sys, datetime, operator, networkx, copy
from sets import Set

def process_file (dirname, filename, authors, messages):
    fullfname=os.path.join(dirname, filename)
    sys.stderr.write ("processing "+fullfname+"\n")

    tmp=re.match ("([0-9]{4})-([0-9]{2})-([0-9]{2}).ubuntu.txt", filename)
    year=int(tmp.group(1))
    month=int(tmp.group(2))
    day=int(tmp.group(3))

    f=open(fullfname,"r")
 
    while True:
        raw=f.readline()
        l=raw.rstrip ()
        if len(l)==0:
            break

        tmp=re.match ("\[([0-9]{2}):([0-9]{2})\] <([^ ]*)> (.*)", l)
        #if tmp==None:
        #    print "unparsed: "+l
        if tmp!=None:
            hour=int(tmp.group(1))
            minute=int(tmp.group(2))
            author=tmp.group(3)
	    authors.add(author)
            #TS=datetime.datetime(year, month, day, hour, minute)
            TS=(year, month, day, hour, minute)
	    msg=tmp.group(4)
	    messages.append((TS,author, msg))

    f.close()

# command-line: <path_to_logs>
authors=Set()
messages=[]
for dirname, dirnames, filenames in os.walk(sys.argv[1]):
    for filename in filenames:
        process_file (dirname, filename, authors, messages)

print "authors=", len(authors)
print "messages=", len(messages)
    
pairs={}

for TS, author, msg in messages:
    tmp=re.match ("^(.+): (.+?)$", msg) # second part is greedy
    if tmp!=None:
        to=tmp.group(1)
	msg_rest=tmp.group(2)
	if to in authors:
	    pair=(author, to)
	    if pair not in pairs:
                pairs[pair]=Set()
	    pairs[pair].add((TS[0], TS[1], TS[2]))

G=networkx.Graph()
for pair in pairs:
    if len(pairs[pair])>10: # at least 11 different days
	if len(Set(map (lambda x: (x[0], x[1]), pairs[pair])))>5: # at least 6 different months
            G.add_node(pair[0])
            G.add_node(pair[1])
            G.add_edge(pair[0], pair[1])

all_cliques=list(networkx.algorithms.clique.find_cliques(G))
filtered_cliques=filter(lambda x: len(x) > 2, all_cliques)
sorted_cliques=sorted(filtered_cliques, key=len, reverse=True)
 
for c in sorted_cliques:
    print "* clique size", len(c)
    print c
