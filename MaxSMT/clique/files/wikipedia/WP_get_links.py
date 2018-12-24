#-*- coding: utf-8 -*-

# Python 2.7

from lxml import etree
from sets import Set
import sys, time, re, os

RX_ANY_CHAR_EXCEPT_RIGHT_SQUARE_BRACKET='[^\]]'
RX_ANY_CHAR_EXCEPT_PIPE_AND_RIGHT_SQUARE_BRACKET='[^\]\|]'
RX_ANY_STRING_EXCEPT_RIGHT_SQUARE_BRACKET='('+RX_ANY_CHAR_EXCEPT_RIGHT_SQUARE_BRACKET+'*)'
RX_ANY_STRING_EXCEPT_PIPE_AND_RIGHT_SQUARE_BRACKET='('+RX_ANY_CHAR_EXCEPT_PIPE_AND_RIGHT_SQUARE_BRACKET+'*)'

def process_file (fname):
    links=Set()
    #redirects={}
    current_tags=[]
    tmp="{http://www.mediawiki.org/xml/export-0.10/}"
    namespaces = []
    cur_title=""

    context = etree.iterparse(fname, events=("start", "end", "start-ns", "end-ns"))
    for event, elem in context:
        if event=="start-ns":
            namespaces.insert(0, elem)
        
        if event=="end-ns":
            namespaces.pop(0)

        if event=="start":
            current_tags.append (elem.tag)
         
        if event=="end":
            if current_tags[-1]!=elem.tag:
                raise AssertionError
            current_tags.pop()

            if elem.tag==tmp+"title":
		cur_title=elem.text

            if elem.tag==tmp+"text":
                if elem.text!=None: # FIXME
                    if elem.text.startswith('#REDIRECT'):
                        m=re.search('#REDIRECT \[\['+RX_ANY_STRING_EXCEPT_RIGHT_SQUARE_BRACKET+'\]\]', elem.text)
                        if m!=None: # FIXME!
                            print "REDIRECT |", cur_title.encode('utf-8'), "|", m.group(1).encode ('utf-8')
                    else:
                        # find all [[link]]
                        m = re.findall('\[\['+RX_ANY_STRING_EXCEPT_PIPE_AND_RIGHT_SQUARE_BRACKET+'\]\]', elem.text)
                        for x in m:
			    if x.startswith('#')==False:
                                links.add(x)

                        # find all [[link|text]]
                        m = re.findall('\[\['+RX_ANY_STRING_EXCEPT_PIPE_AND_RIGHT_SQUARE_BRACKET+'\|'+RX_ANY_STRING_EXCEPT_RIGHT_SQUARE_BRACKET+'\]\]', elem.text)
                        for x in m:
			    if x[0].startswith('#')==False:
                                links.add(x[0].split('#')[0]) # handle links like [[article#anchor]]

            if elem.tag==tmp+"page":
                pass
            elem.clear()
	    for l in links:
                print "LINK |", cur_title.encode('utf-8'), "|", l.encode ('utf-8')
	    links.clear()

process_file(sys.argv[1])

