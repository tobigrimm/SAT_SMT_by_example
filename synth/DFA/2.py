from z3 import *
import sys, random, os

DIVISOR=3
#DIVISOR=5
#DIVISOR=7
#DIVISOR=9
#DIVISOR=10
#DIVISOR=11 # no luck

state=[[Int('state_%d_%d' % (s, b)) for b in range(2)] for s in range(100)]

INITIAL_STATE=0
INVALID_STATE=999

# construct FA for z3
def transition (STATES, s, i):
    # this is like switch()

    rt=IntVal(INVALID_STATE)
    for j in range(STATES):
        rt=If(And(s==IntVal(j), i==0), state[j][0], rt)
        rt=If(And(s==IntVal(j), i==1), state[j][1], rt)
    return rt

# construct FA for z3
def FA(STATES, input_string):
    s=IntVal(INITIAL_STATE)
    for i in input_string:
        s=transition(STATES, s, int(i))
    return s

# simulate FA for testing purpose:
def simulate_FA(input_, FA):
    s=INITIAL_STATE
    for i in input_:
        if i=='0':
            s=FA[s][0]
        else:
            s=FA[s][1]
    return s

def test_FA (STATES, FA):
    ACCEPTING_STATE=STATES-1
    for i in range(10000):
        rnd=random.randint(1,100000000000000)
        b=bin(rnd)[2:]
        final_state=simulate_FA(b, FA)
        if (rnd % DIVISOR)==0:
            if final_state!=ACCEPTING_STATE:
                raise AssertionError
        else:
            if final_state==ACCEPTING_STATE:
                raise AssertionError
    print "test OK"

def print_model(STATES, m):
    print "[state, input, new state]"
    for i in range(STATES):
        print "[%d, \"0\", %d]," % (i, m[state[i][0]].as_long())
        print "[%d, \"1\", %d]," % (i, m[state[i][1]].as_long())

    f=open("1.gv", "wt")
    f.write("digraph finite_state_machine {\n")
    f.write("\trankdir=LR;\n")
    f.write("\tsize=\"8,5\"\n")
    f.write("\tnode [shape = doublecircle]; S_0 S_"+str(STATES-1)+";\n");
    f.write("\tnode [shape = circle];\n");
 
    FA={}
    for s in range(STATES):
        f.write("\tS_%d -> S_%d [ label = \"0\" ];\n" % (s, m[state[s][0]].as_long()))
        f.write("\tS_%d -> S_%d [ label = \"1\" ];\n" % (s, m[state[s][1]].as_long()))
        FA[s]=(m[state[s][0]].as_long(), m[state[s][1]].as_long())
    f.write("}\n")
    f.close()
    os.system("dot -Tpng 1.gv > 1.png") # run GraphViz
    test_FA (STATES, FA)

def attempt(STATES):
    print "STATES=", STATES
    sl=Solver()
    # Z3 multithreading, starting at 4.8.x:
    set_param("parallel.enable", True)

    for s in range(STATES):
        for b in range(2):
            sl.add(And(state[s][b]>=0, state[s][b]<STATES))

    ACCEPTING_STATE=STATES-1

    # may be lower for low DIVISOR's like 3 or 5.
    # but 256 is safe choice for DIVISOR's up to 9
    for i in range(256):
        b=bin(i)[2:]
        if (i % DIVISOR)==0:
            sl.add(FA(STATES, b)==ACCEPTING_STATE)
        else:
            sl.add(FA(STATES, b)!=ACCEPTING_STATE)

    result=[]

    if sl.check() == unsat:
        return
    m = sl.model()
    print_model(STATES, m)
    exit(0)

for i in range(2, 100):
    attempt(i)

