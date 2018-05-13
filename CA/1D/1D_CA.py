from z3 import *

WIDTH=15

def _try (RULE, STATES, WRAPPED, SHIFTED):

    rules=[]
    for i in range(8):
        if ((RULE>>i)&1)==1:
            rules.append(True)
        else:
            rules.append(False)

    rules=rules[::-1]
    #print "rules=", rules

    def f(a, b, c):
        return If(And(a==True, b==True, c==True), rules[7],
            If(And(a==True, b==True, c==False), rules[6],
            If(And(a==True, b==False, c==True), rules[5],
            If(And(a==True, b==False, c==False), rules[4],
            If(And(a==False, b==True, c==True), rules[3],
            If(And(a==False, b==True, c==False), rules[2],
            If(And(a==False, b==False, c==True), rules[1],
            If(And(a==False, b==False, c==False), rules[0], False))))))))

    S=[[Bool("%d_%d" % (s, i)) for i in range(WIDTH)] for s in range(STATES)]

    s=Solver()

    if WRAPPED==False:
        for st in range(STATES):
           s.add(S[st][0]==False)
           s.add(S[st][WIDTH-1]==False)

    #s.add(S[0][15]==True)

    if WRAPPED==False:
        for st in range(1,STATES):
            for i in range(1, WIDTH-1):
                s.add(S[st][i] == f(S[st-1][i-1], S[st-1][i], S[st-1][i+1]))
    else:
        for st in range(1,STATES):
            for i in range(WIDTH):
                s.add(S[st][i] == f(S[st-1][(i-1) % WIDTH], S[st-1][i], S[st-1][(i+1) % WIDTH]))

    def is_empty(st):
        t=[]
        for i in range(WIDTH):
            t.append(S[st][i]==False)
        return And(*t)
    
    def is_full(st):
        t=[]
        for i in range(WIDTH):
            t.append(S[st][i]==True)
        return And(*t)

    def non_equal_states (st1, st2):
        t=[]
        for i in range(WIDTH):
            t.append(S[st1][i] != S[st2][i])
        return Or(*t)

    #s.add(non_equal_states(0, 1))

    for st in range(STATES):
        s.add(is_empty(st)==False)
        s.add(is_full(st)==False)

    # first and last states are equal to each other:
    if WRAPPED==False:
        for i in range(1,WIDTH-1):
            if SHIFTED==0:
                s.add(S[0][i]==S[STATES-1][i])
            if SHIFTED==1:
                s.add(S[0][i]==S[STATES-1][i-1])
            if SHIFTED==2:
                s.add(S[0][i]==S[STATES-1][i+1])
    else:
        for i in range(WIDTH):
            if SHIFTED==0:
                s.add(S[0][i]==S[STATES-1][i % WIDTH])
            if SHIFTED==1:
                s.add(S[0][i]==S[STATES-1][(i-1) % WIDTH])
            if SHIFTED==2:
                s.add(S[0][i]==S[STATES-1][(i+1) % WIDTH])

    if s.check()==unsat:
        return
        #print "unsat"
        #exit(0)

    m=s.model()

    print "RULE=%d STATES=%d, WRAPPED=%s, SHIFTED=%d" % (RULE, STATES, str(WRAPPED), SHIFTED)
    for st in range(STATES):
        t=""
        for i in range(WIDTH):
            if str(m[S[st][i]])=="False":
                t=t+"."
            else:
                t=t+"*"
        print t

for RULE in range(0, 256):
    for STATES in range(2, 10):
        if True:
        #for WRAPPED in [False, True]:
            WRAPPED=True
            for SHIFTED in [0,1,2]:
                _try (RULE, STATES, WRAPPED, SHIFTED)

