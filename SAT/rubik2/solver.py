#-*- coding: utf-8 -*-

#!/usr/bin/env python

import subprocess, os, frolic, Xu

BITS_PER_COLOR=3
BITS_PER_SELECTOR=5

def alloc_facelets_and_selectors(states):
    global facelets, selectors, s

    facelets=[dict() for x in range(states)]

    for state in range(states):
        for prefix in "FUDRLB":
            # allocate variables for each face:
            facelets[state][prefix+"1"]=s.alloc_BV(BITS_PER_COLOR)
            facelets[state][prefix+"2"]=s.alloc_BV(BITS_PER_COLOR)
            facelets[state][prefix+"3"]=s.alloc_BV(BITS_PER_COLOR)
            facelets[state][prefix+"4"]=s.alloc_BV(BITS_PER_COLOR)

    selectors=[None]*(TURNS)
    for step in range(TURNS):
        selectors[step]=s.alloc_BV(BITS_PER_SELECTOR)

# src=list of 18 facelets
def add_r(dst, src):
    global facelets, selectors, s
    for state in range(STATES-1):
        src_vectors=[]
        for tmp in src:
            src_vectors.append(facelets[state][tmp])

        # padding: there are 18 used MUX inputs, so add 32-18=14 for padding
        for i in range(32-18): 
            src_vectors.append([s.const_true,s.const_true,s.const_true])

        dst_vector=s.create_wide_MUX (src_vectors, selectors[state])
        s.fix_BV_EQ(dst_vector,facelets[state+1][dst])

def encode_color(color):
    return {"W":[0,0,1], "G":[0,1,0], "B":[0,1,1], "O":[1,0,0], "R":[1,0,1], "Y": [1,1,0]}[color]

def set_state(step, d):
    global s
    for k in d.keys():
        s.fix_BV(facelets[step][k+"1"], encode_color(d[k][0]))
        s.fix_BV(facelets[step][k+"2"], encode_color(d[k][1]))
        s.fix_BV(facelets[step][k+"3"], encode_color(d[k][2]))
        s.fix_BV(facelets[step][k+"4"], encode_color(d[k][3]))

def do_all(turns):
    global s, TURNS, STATES, facelets, selectors

    TURNS=turns
    STATES=TURNS+1
    facelets=None
    selectors=None

    s=Xu.Xu(False)

    alloc_facelets_and_selectors(STATES)

    # solved state:
    set_state(STATES-1, {"F":"WWWW", "U":"GGGG", "D":"BBBB", "R":"OOOO", "L":"RRRR", "B":"YYYY"})

    # 4: rdur, 2 solutions (picosat)
    set_state(0, {"F":"RYOG", "U":"YRGO", "D":"WRBO", "R":"GYWB", "L":"BYWG", "B":"BOWR"})

    # other tests:
    
    # 9 or less 
    #set_state(0, {"F":"OROB", "U":"GYGG", "D":"BRWO", "R":"WGYY", "L":"RWRW", "B":"OYBB"})

    # 5
    #set_state(0, {"F":"BROW", "U":"YWOB", "D":"WROY", "R":"YGBG", "L":"BWYG", "B":"RORG"})
   
    # 5 
    #set_state(0, {"F":"RYOG", "U":"YBGO", "D":"WRBW", "R":"GOWB", "L":"RYYG", "B":"WBRO"})

    # 1 (RCW)
    #set_state(0, {"F":"WGWG", "U":"GYGY", "D":"BWBW", "R":"OOOO", "L":"RRRR", "B":"BYBY"})

    # 9 or less
    #set_state(0, {"F":"ROWB", "U":"RYYB", "D":"RYWG", "R":"WGOR", "L":"WBOG", "B":"OBYG"})

    # 6, 2 solutions (picosat)...
    #set_state(0, {"F":"RBGW", "U":"YRGW", "D":"YGWB", "R":"OBRO", "L":"RYOO", "B":"WBYG"})

    # 4, 1 solution (picosat)!
    #set_state(0, {"F":"GGYB", "U":"GRRY", "D":"RWBO", "R":"OGRY", "L":"OWOB", "B":"YWBW"})
    
    # 6, 6 solutions (picosat)
    #set_state(0, {"F":"GRRB", "U":"YYWY", "D":"WOBW", "R":"GGWR", "L":"BORB", "B":"OOGY"})

    # 6, 3 solutions (picosat)
    #set_state(0, {"F":"RWBG", "U":"BWYR", "D":"WYYO", "R":"GORG", "L":"RBOO", "B":"GWYB"})
    
    # 3 or less
    #set_state(0, {"F":"RORW", "U":"BRBB", "D":"GOOR", "R":"WYGY", "L":"OWYW", "B":"BYGG"})
    
    # 4
    #set_state(0, {"F":"RBRO", "U":"WGWY", "D":"YWOB", "R":"RWBO", "L":"BGYG", "B":"ORYG"})
    
    # 8
    #set_state(0, {"F":"GBOO", "U":"BBRO", "D":"BYGY", "R":"YWGG", "L":"YWWW", "B":"RRRO"})

    # 8
    #set_state(0, {"F":"BGBO", "U":"GWYR", "D":"YGYO", "R":"YRWB", "L":"WOGR", "B":"BRWO"})

    # 3 or less
    #set_state(0, {"F":"GRBG", "U":"BYOG", "D":"WYOY", "R":"WORR", "L":"RYGO", "B":"BWBW"})

    # 7
    #set_state(0, {"F":"BBWY", "U":"OGOR", "D":"ROYY", "R":"WYBO", "L":"WWBG", "B":"RGGR"})

    # 8
    #set_state(0, {"F":"YRRO", "U":"WWBY", "D":"WYWB", "R":"GBGO", "L":"RROB", "B":"OGYG"})

    # 3 or less (stuck)
    # set_state(0, {"F":"OWBB", "U":"RYBG", "D":"RORG", "R":"ORWY", "L":"BYWW", "B":"GYOG"})

    # 9 or less
    # set_state(0, {"F":"GGRW", "U":"BBYO", "D":"GRBO", "R":"WYBG", "L":"WRRW", "B":"OOYY"})
 
    # 8 or less
    #set_state(0, {"F":"WBRG", "U":"RGBR", "D":"GORB", "R":"WWYO", "L":"YOYW", "B":"OGYB"})

    # 8
    #set_state(0, {"F":"GOWW", "U":"RYRG", "D":"GRBY", "R":"YOBG", "L":"BWOO", "B":"BYRW"})

    # FCW, RCW
    #set_state(0, {"F":"WOWB", "U":"GWRW", "D":"OYBY", "R":"GGOO", "L":"RBRB", "B":"RYGY"})

    # 9
    #set_state(0, {"F":"YOWY", "U":"OGGY", "D":"OBGR", "R":"BRRW", "L":"WOYB", "B":"WGBR"})

    # 1 F
    #set_state(0, {"F":"WWWW", "U":"GGRR", "D":"OOBB", "R":"GOGO", "L":"RBRB", "B":"YYYY"})    

    # 2 BCW / FCCW
    #set_state(0, {"F":"WWWW", "U":"RRRR", "D":"OOOO", "R":"GGGG", "L":"BBBB", "B":"YYYY"})

    # 4 RDUR, but backwards: RCCW UCCW DCCW RCCW
    #set_state(0, {"F":"OBRY", "U":"GOWR", "D":"BOYR", "R":"WGBY", "L":"WBGY", "B":"WRGO"})

    # 2, UCCW / DCW
    #set_state(0, {"F":"OOOO", "U":"GGGG", "D":"BBBB", "R":"YYYY", "L":"WWWW", "B":"RRRR"})

    # 2, RCCW / LCW
    #set_state(0, {"F":"BBBB", "U":"WWWW", "D":"YYYY", "R":"OOOO", "L":"RRRR", "B":"GGGG"})

    # 1, UCCW
    #set_state(0, {"F":"OOWW", "U":"GGGG", "D":"BBBB", "R":"YYOO", "L":"WWRR", "B":"RRYY"})

    # 1, UCW
    #set_state(0, {"F":"RRWW", "U":"GGGG", "D":"BBBB", "R":"WWOO", "L":"YYRR", "B":"OOYY"})

    # 1, RCCW
    #set_state(0, {"F":"WBWB", "U":"GWGW", "D":"BYBY", "R":"OOOO", "L":"RRRR", "B":"GYGY"})

    # 1, RCW
    #set_state(0, {"F":"WGWG", "U":"GYGY", "D":"BWBW", "R":"OOOO", "L":"RRRR", "B":"BYBY"})

    # 1, DCCW
    #set_state(0, {"F":"WWRR", "U":"GGGG", "D":"BBBB", "R":"OOWW", "L":"RRYY", "B":"YYOO"})

    # 1. DCW
    #set_state(0, {"F":"WWOO", "U":"GGGG", "D":"BBBB", "R":"OOYY", "L":"RRWW", "B":"YYRR"})

    # 1 LCCW
    #set_state(0, {"F":"GWGW", "U":"YGYG", "D":"WBWB", "R":"OOOO", "L":"RRRR", "B":"YBYB"})

    # 1 LCW
    #set_state(0, {"F":"BWBW", "U":"WGWG", "D":"YBYB", "R":"OOOO", "L":"RRRR", "B":"YGYG"})

    # 1 FCCW
    #set_state(0, {"F":"WWWW", "U":"GGRR", "D":"OOBB", "R":"GOGO", "L":"RBRB", "B":"YYYY"})

    # 1. FCW
    #set_state(0, {"F":"WWWW", "U":"GGOO", "D":"RRBB", "R":"BOBO", "L":"RGRG", "B":"YYYY"})

    # 1 BCCW
    #set_state(0, {"F":"WWWW", "U":"OOGG", "D":"BBRR", "R":"OBOB", "L":"GRGR", "B":"YYYY"})

    # 1. BCW
    #set_state(0, {"F":"WWWW", "U":"RRGG", "D":"BBOO", "R":"OGOG", "L":"BRBR", "B":"YYYY"})    

    # 3 or less. right top corner rotated CW, left top rotated CCW
    #set_state(0, {"F":"ROWW", "U":"GGWW", "D":"BBBB", "R":"GOOO", "L":"RGRR", "B":"YYYY"})

    # 8
    #set_state(0, {"F":"RWWY", "U":"YOWB", "D":"OOOR", "R":"RYBY", "L":"RGGB", "B":"GBGW"})

    #      dst,  FCW  FH   FCCW UCW  UH   UCCW DCW  DH   DCCW RCW  RH   RCCW LCW  LH   LCCW BCW  BH   BCCW
    add_r("F1",["F3","F4","F2","R1","B1","L1","F1","F1","F1","F1","F1","F1","U1","B4","D1","F1","F1","F1"])
    add_r("F2",["F1","F3","F4","R2","B2","L2","F2","F2","F2","D2","B3","U2","F2","F2","F2","F2","F2","F2"])
    add_r("F3",["F4","F2","F1","F3","F3","F3","L3","B3","R3","F3","F3","F3","U3","B2","D3","F3","F3","F3"])
    add_r("F4",["F2","F1","F3","F4","F4","F4","L4","B4","R4","D4","B1","U4","F4","F4","F4","F4","F4","F4"])
    add_r("U1",["U1","U1","U1","U3","U4","U2","U1","U1","U1","U1","U1","U1","B4","D1","F1","R2","D4","L3"])
    add_r("U2",["U2","U2","U2","U1","U3","U4","U2","U2","U2","F2","D2","B3","U2","U2","U2","R4","D3","L1"])
    add_r("U3",["L4","D2","R1","U4","U2","U1","U3","U3","U3","U3","U3","U3","B2","D3","F3","U3","U3","U3"])
    add_r("U4",["L2","D1","R3","U2","U1","U3","U4","U4","U4","F4","D4","B1","U4","U4","U4","U4","U4","U4"])
    add_r("D1",["R3","U4","L2","D1","D1","D1","D3","D4","D2","D1","D1","D1","F1","U1","B4","D1","D1","D1"])
    add_r("D2",["R1","U3","L4","D2","D2","D2","D1","D3","D4","B3","U2","F2","D2","D2","D2","D2","D2","D2"])
    add_r("D3",["D3","D3","D3","D3","D3","D3","D4","D2","D1","D3","D3","D3","F3","U3","B2","L1","U2","R4"])
    add_r("D4",["D4","D4","D4","D4","D4","D4","D2","D1","D3","B1","U4","F4","D4","D4","D4","L3","U1","R2"])
    add_r("R1",["U3","L4","D2","B1","L1","F1","R1","R1","R1","R3","R4","R2","R1","R1","R1","R1","R1","R1"])
    add_r("R2",["R2","R2","R2","B2","L2","F2","R2","R2","R2","R1","R3","R4","R2","R2","R2","D4","L3","U1"])
    add_r("R3",["U4","L2","D1","R3","R3","R3","F3","L3","B3","R4","R2","R1","R3","R3","R3","R3","R3","R3"])
    add_r("R4",["R4","R4","R4","R4","R4","R4","F4","L4","B4","R2","R1","R3","R4","R4","R4","D3","L1","U2"])
    add_r("L1",["L1","L1","L1","F1","R1","B1","L1","L1","L1","L1","L1","L1","L3","L4","L2","U2","R4","D3"])
    add_r("L2",["D1","R3","U4","F2","R2","B2","L2","L2","L2","L2","L2","L2","L1","L3","L4","L2","L2","L2"])
    add_r("L3",["L3","L3","L3","L3","L3","L3","B3","R3","F3","L3","L3","L3","L4","L2","L1","U1","R2","D4"])
    add_r("L4",["D2","R1","U3","L4","L4","L4","B4","R4","F4","L4","L4","L4","L2","L1","L3","L4","L4","L4"])
    add_r("B1",["B1","B1","B1","L1","F1","R1","B1","B1","B1","U4","F4","D4","B1","B1","B1","B3","B4","B2"])
    add_r("B2",["B2","B2","B2","L2","F2","R2","B2","B2","B2","B2","B2","B2","D3","F3","U3","B1","B3","B4"])
    add_r("B3",["B3","B3","B3","B3","B3","B3","R3","F3","L3","U2","F2","D2","B3","B3","B3","B4","B2","B1"])
    add_r("B4",["B4","B4","B4","B4","B4","B4","R4","F4","L4","B4","B4","B4","D1","F1","U1","B2","B1","B3"])

    if s.solve()==False:
        print "unsat!"
        exit(0)
    
    turn_name=["FCW","FH","FCCW","UCW","UH","UCCW","DCW","DH","DCCW","RCW","RH","RCCW","LCW","LH","LCCW","BCW","BH","BCCW"]

    print "sat!"
    for turn in selectors:
        # 'turn' is array of 5 variables
        # convert each variable to "1" or "0" string and create 5-digit string:
        rt="".join([str(s.get_var_from_solution(bit)) for bit in turn])
        # reverse string, convert it to integer and use it as index for array to get a move name:
        print turn_name[int(frolic.rvr(rt),2)]

    print ""

def main():
    for i in range(11,0,-1):
        print "TURNS=", i
        do_all(i)

main()

