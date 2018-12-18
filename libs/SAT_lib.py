#!/usr/bin/env python3

# my own SAT/CNF library

# dennis(a)yurichev, 2017-2018

# "BV" stands for bitvector

# TODO: check signed/unsigned issues for adder/multiplier/divider
# TODO: class instance, class term
# TODO: get rid of *fix* functions?

import subprocess, os, itertools
import my_utils

# BV=[MSB...LSB]
def BV_to_number(BV):
    # coeff=1, 2^1, 2^2 ... 2^(len(BV)-1)
    coeff=1
    rt=0
    for v in my_utils.rvr(BV):
        rt=rt+coeff*v
        coeff=coeff*2
    return rt

# bit order: [MSB..LSB]
# 'size' is desired width of bitvector, in bits:
def n_to_BV (n, size):
    out=[0]*size
    i=0
    for var in my_utils.rvr(bin(n)[2:]):
        if var=='1':
            out[i]=1
        else:
            out[i]=0
        i=i+1
    return my_utils.rvr(out)

class SAT_lib:

    def __init__(self, maxsat):
        self.last_var=1
        # just list of lines to be written to CNF-file:
        self.CNF=[]
        self.clauses_total=0
        self.HARD_CLAUSE=10000

        self.maxsat=maxsat

        #self.SAT_SOLVER="minisat"

        self.remove_CNF_file=True
        #self.remove_CNF_file=False

        self.verbosity=0

        # allocate a single variable fixed to False:
        self.const_false=self.create_var()
        self.fix(self.const_false,False)
        # allocate a single variable fixed to True:
        self.const_true=self.create_var()
        self.fix(self.const_true,True)

    def run_minisat (self):
        child = subprocess.Popen(["minisat", self.CNF_fname, "results.txt"], stdout=subprocess.PIPE)
        child.wait()
        # 10 is SAT, 20 is UNSAT
        if child.returncode==20:
            os.remove ("results.txt")
            return None

        if child.returncode!=10:
            print ("(minisat) unknown retcode: ", child.returncode)
            exit(0)

        solution=my_utils.read_lines_from_file("results.txt")[1].split(" ")
        # remove last "variable", which is 0
        assert solution[-1]=='0'
        solution=solution[:-1]
        os.remove ("results.txt")

        return solution
    
    # cmd_line is an array
    def run_plingeling_or_open_wbo (self, cmd_line):
        tmp_fname="tmp.out"
        logfile=open(tmp_fname, "w")
        child = subprocess.Popen(cmd_line, stdout=logfile)

        child.wait()
        logfile.flush()
        logfile.close()

        tmp=[]
        logfile=open(tmp_fname, "r")
        while True:
            line = logfile.readline()
            if line.startswith("s UNSAT"):
                logfile.close()
                return None
            elif line.startswith("v "):
                tmp.append (line[2:].rstrip())
            elif line=='':
                break
            else:
                pass

        logfile.close()
        os.remove(tmp_fname)
        solution=" ".join(tmp).split(" ")
        return solution

    def run_plingeling (self):
        return self.run_plingeling_or_open_wbo(["plingeling", self.CNF_fname])

    def run_sat_solver(self):
        #return self.run_minisat()
        return self.run_plingeling()

    def run_open_wbo_solver (self):
        return self.run_plingeling_or_open_wbo(["open-wbo", "-algorithm=1", self.CNF_fname])

    def run_maxsat_solver (self):
        return self.run_open_wbo_solver()

    def write_CNF(self):
        if self.maxsat==False:
            self.CNF_fname="1.cnf"
        else:
            self.CNF_fname="1.wcnf"

        VARS_TOTAL=self.last_var-1
        f=open(self.CNF_fname, "w")
        if self.maxsat==False:
            f.write ("p cnf "+str(VARS_TOTAL)+" "+str(self.clauses_total)+"\n")
        else:
            f.write ("p wcnf "+str(VARS_TOTAL)+" "+str(self.clauses_total)+" "+str(self.HARD_CLAUSE)+"\n")
        for line in self.CNF:
            f.write(line)
        f.close()
        if self.verbosity>0:
            print ("write_CNF() clauses=%d" % self.clauses_total)

    def create_var(self):
        self.last_var=self.last_var+1
        return str(self.last_var-1)

    def neg(self, v):
        #print ("neg:", v)
        if type(v)==list:
            raise AssertionError
        if v==None:
            raise AssertionError
        if v=="0":
            raise AssertionError
        # double negation?
        if v.startswith("-"):
            return v[1:]
        return "-"+v

    def neg_if(self, cond, var):
        if cond:
            return self.neg(var)
        else:
            return var

    def BV_neg(self, lst):
        return [self.neg(l) for l in lst]

    def add_comment(self, comment):
        self.CNF.append("c "+comment+"\n")

    def add_clause(self, cls):
        self.clauses_total=self.clauses_total+1
        if self.maxsat==False:
            self.CNF.append(" ".join(cls) + " 0\n")
        else:
            self.CNF.append(str(self.HARD_CLAUSE) + " " + " ".join(cls) + " 0\n")

    def add_soft_clause(self, cls, weight):
        assert self.maxsat==True
        self.clauses_total=self.clauses_total+1
        self.CNF.append(str(weight) + " " + " ".join(cls) + " 0\n")

    def AND_Tseitin(self, v1, v2, out):
        self.add_clause([self.neg(v1), self.neg(v2), out])
        self.add_clause([v1, self.neg(out)])
        self.add_clause([v2, self.neg(out)])
    
    def AND(self,v1, v2):
        out=self.create_var()
        self.AND_Tseitin(v1, v2, out)
        return out
    
    def AND_list(self, l):
        assert(len(l)>=2)
        if len(l)==2:
            return self.AND(l[0], l[1])
        return self.AND(l[0], self.AND_list(l[1:]))

    def BV_AND(self, x,y):
        rt=[]
        for pair in zip(x, y):
            rt.append(self.AND(pair[0],pair[1]))
        return rt
    
    # vals=list
    # as in Tseitin transformations.
    # N.B.: previously called "OR"
    def OR_list(self, vals):
        out=self.create_var()
        self.add_clause(vals+[self.neg(out)])
        for v in vals:
            self.add_clause([self.neg(v), out])
        return out

    def OR_always(self, vals):
        self.add_clause(vals)
    
    def alloc_BV(self, n):
        return [self.create_var() for i in range(n)]
    
    def fix_soft(self, var, b, weight):
        if b==True or b==1:
            self.add_soft_clause([var], weight)
        else:
            self.add_soft_clause([self.neg(var)], weight)

    def fix_soft_always_true(self, var, weight):
        self.fix_soft(var, True, weight)

    def fix_soft_always_true_all_bits_in_BV(self, BV, weight):
        for b in BV:
            self.fix_soft_always_true(b, weight)
    
    def fix(self, var, b):
        if b==True or b==1:
            self.add_clause([var])
        else:
            self.add_clause([self.neg(var)])

    def fix_always_false(self, var):
        self.fix(var, False)

    def fix_always_true(self, var):
        self.fix(var, True)
    
    # BV is a list of True/False/0/1
    def fix_BV(self, _vars, BV):
        #print _vars, BV
        assert len(_vars)==len(BV)
        for var, _bool in zip(_vars, BV):
            self.fix (var, _bool)

    # BV is a list of True/False/0/1
    def fix_BV_soft(self, _vars, BV, weight):
        assert len(_vars)==len(BV)
        for var, _bool in zip(_vars, BV):
            self.fix_soft (var, _bool, weight)

    def get_var_from_solution(self, var):
        # 1 if var is present in solution, 0 if present in negated form:
        if var in self.solution:
            return 1
        if "-"+var in self.solution:
            return 0
        print "get_var_from_solution(): incorrect var number: ", var
        raise AssertionError # incorrect var number
    
    def get_BV_from_solution(self, BV):
        return [self.get_var_from_solution(var) for var in BV]
    
    def solve(self):
        self.write_CNF()
        if self.maxsat:
            self.solution=self.run_maxsat_solver()
        else:
            self.solution=self.run_sat_solver()
        if self.remove_CNF_file:
            os.remove(self.CNF_fname)
        if self.solution==None:
            return False
        else:
            return True

    def NOT(self, x):
        rt=self.create_var()
        self.add_clause([self.neg(rt), self.neg(x)])
        self.add_clause([rt, x])
        return rt

    def BV_NOT(self, x):
        rt=[]
        for b in x:
            rt.append(self.NOT(b))
        return rt
    
    def XOR(self,x,y):
        rt=self.create_var()
        self.add_clause([self.neg(x), self.neg(y), self.neg(rt)])
        self.add_clause([x, y, self.neg(rt)])
        self.add_clause([x, self.neg(y), rt])
        self.add_clause([self.neg(x), y, rt])
        return rt
    
    def BV_XOR(self,x,y):
        rt=[]
        for pair in zip(x,y):
            rt.append(self.XOR(pair[0], pair[1]))
        return rt

    def BV_XOR_list(self, l):
        assert(len(l)>=2)
        if len(l)==2:
            return self.BV_XOR(l[0], l[1])
        return self.BV_XOR(l[0], self.BV_XOR_list(l[1:]))
    
    def EQ(self, x, y):
        return self.NOT(self.XOR(x,y))
    
    def NEQ(self, x, y):
        return self.XOR(x,y)

    # naive/pairwise encoding   
    def AtMost1(self, lst):
        for pair in itertools.combinations(lst, r=2):
            self.add_clause([self.neg(pair[0]), self.neg(pair[1])])
       
    # previously named POPCNT1 
    # make one-hot (AKA unitary) variable
    def make_one_hot(self, lst):
        self.AtMost1(lst)
        self.OR_always(lst)

    def neg_nth_elem_in_lst(self, lst, n):
        rt=[]
        assert n<len(lst)
        for i in range(len(lst)):
            if i==n:
                rt.append(self.neg(lst[i]))
            else:
                rt.append(lst[i])
        return rt

    # sum of variables must not be equal to 1, but can be 0
    def SumIsNot1(self, lst):
        for i in range(len(lst)):
            self.add_clause(self.neg_nth_elem_in_lst(lst, i))
    
    # Hamming distance between two bitvectors is 1
    # i.e., two bitvectors differ in only one bit.
    def hamming1(self,l1, l2):
        self.add_comment("hamming1")
        assert len(l1)==len(l2)
        XORed=self.BV_XOR(l1, l2)
        self.make_one_hot(XORed)

    def fix_EQ(self, v1, v2):
        self.add_clause([self.neg(v1), v2])
        self.add_clause([v1, self.neg(v2)])
    
    # bitvectors must be equal to each other.
    def fix_BV_EQ(self, l1, l2):
        #print len(l1), len(l2)
        assert len(l1)==len(l2)
        self.add_comment("fix_BV_EQ")
        for p in zip(l1, l2):
            self.fix_EQ(p[0], p[1])

    def BV_EQ(self, l1, l2):
        #print len(l1), len(l2)
        assert len(l1)==len(l2)
        self.add_comment("BV_EQ")
        t=[]
        for p in zip(l1, l2):
            t.append(self.NOT(self.EQ(p[0], p[1])))
        return self.NOT(self.OR_list(t))
    
    # bitvectors must be different.
    def fix_BV_NEQ(self, l1, l2):
        #print len(l1), len(l2)
        assert len(l1)==len(l2)
        self.add_comment("fix_BV_NEQ")
        t=[self.XOR(l1[i], l2[i]) for i in range(len(l1))]
        self.add_clause(t)

    # full-adder, as found by Mathematica using truth table:
    def FA (self, a,b,cin):
        s=self.create_var()
        cout=self.create_var()

        self.add_clause([self.neg(a), self.neg(b), self.neg(cin), s])
        self.add_clause([self.neg(a), self.neg(b), cout])
        self.add_clause([self.neg(a), self.neg(cin), cout])
        self.add_clause([self.neg(a), cout, s])
        self.add_clause([a, b, cin, self.neg(s)])
        self.add_clause([a, b, self.neg(cout)])
        self.add_clause([a, cin, self.neg(cout)])
        self.add_clause([a, self.neg(cout), self.neg(s)])
        self.add_clause([self.neg(b), self.neg(cin), cout])
        self.add_clause([self.neg(b), cout, s])
        self.add_clause([b, cin, self.neg(cout)])
        self.add_clause([b, self.neg(cout), self.neg(s)])
        self.add_clause([self.neg(cin), cout, s])
        self.add_clause([cin, self.neg(cout), self.neg(s)])

        return s, cout

    # bit order: [MSB..LSB]
    # n-bit adder:
    def adder(self, X,Y):
        assert len(X)==len(Y)
        # first full-adder could be half-adder
        # start with lowest bits:
        inputs=my_utils.rvr(list(zip(X,Y)))
        carry=self.const_false
        sums=[]
        for pair in inputs:
            # "carry" variable is replaced at each iteration.
            # so it is used in the each FA() call from the previous FA() call.
            s, carry = self.FA(pair[0], pair[1], carry)
            sums.append(s)
        return my_utils.rvr(sums), carry

    # bit is 0 or 1.
    # i.e., if it's 0, output is 0 (all bits)
    # if it's 1, output=input
    def mult_by_bit(self, X, bit):
        return [self.AND(i, bit) for i in X]

    # bit order: [MSB..LSB]
    # build multiplier using adders and mult_by_bit blocks:
    def multiplier(self, X, Y):
        assert len(X)==len(Y)
        out=[]
        #initial:
        prev=[self.const_false]*len(X)
        # first adder can be skipped, but I left thing "as is" to make it simpler
        for Y_bit in my_utils.rvr(Y):
            s, carry = self.adder(self.mult_by_bit(X, Y_bit), prev)
            out.append(s[-1])
            prev=[carry] + s[:-1]
    
        return prev + my_utils.rvr(out)

    def NEG(self, x):
        # invert all bits
        tmp=self.BV_NOT(x)
        # add 1
        one=self.alloc_BV(len(tmp))
        self.fix_BV(one,n_to_BV(1, len(tmp)))
        return self.adder(tmp, one)[0]

    # untested
    def shift_left (self, x, cnt):
        return x[cnt:]+[self.const_false]*cnt

    def shift_left_1 (self, x):
        return x[1:]+[self.const_false] 

    def shift_right (self, x, cnt):
        return [self.const_false]*cnt+x[cnt:]

    def shift_right_1 (self, x):
        return [self.const_false]+x[:-1]

    def create_MUX(self, ins, sels):
        assert 2**len(sels)==len(ins)
        x=self.create_var()
        for sel in range(len(ins)): # for example, 32 for 5-bit selector
            tmp=[self.neg_if((sel>>i)&1==1, sels[i]) for i in range(len(sels))] # 5 for 5-bit selector
   
            self.add_clause([self.neg(ins[sel])] + tmp + [x])
            self.add_clause([ins[sel]] + tmp + [self.neg(x)])
        return x
    
    # for 1-bit sel
    # ins=[[outputs for sel==0], [outputs for sel==1]]
    def create_wide_MUX (self, ins, sels):
        out=[]
        for i in range(len(ins[0])):
            inputs=[x[i] for x in ins]
            out.append(self.create_MUX(inputs, sels))
        return out

    # untested:
    def ITE(self, s,f,t):
        if s=="0":
            raise AssertionError
        if f=="0":
            raise AssertionError
        if t=="0":
            raise AssertionError
        x=self.create_var()
        if x=="0":
            raise AssertionError
      
        # as found by my util 
        self.add_clause([self.neg(s),self.neg(t),x])
        self.add_clause([self.neg(s),t,self.neg(x)])
        self.add_clause([s,self.neg(f),x])
        self.add_clause([s,f,self.neg(x)])

        return x

    def subtractor(self, minuend, subtrahend):
        # same as adder(), buf: 1) subtrahend is inverted; 2) input carry-in bit is 1
        X=minuend
        Y=self.BV_NOT(subtrahend)

        inputs=my_utils.rvr(list(zip(X,Y)))
        carry=self.const_true
        sums=[]
        for pair in inputs:
            # "carry" variable is replaced at each iteration.
            # so it is used in the each FA() call from the previous FA() call.
            st, carry = self.FA(pair[0], pair[1], carry)
            sums.append(st)

        return my_utils.rvr(sums), carry

    # 0 if a<b
    # 1 if a>=b
    def comparator_GE(self, a, b):
        tmp, carry = self.subtractor(a, b)
        return carry

    def div_blk(self, enable, divident, divisor):
        assert len(divident)==len(divisor)

        diff, _ = self.subtractor(minuend=divident, subtrahend=divisor)

        cmp_res = self.AND(enable, self.comparator_GE(divident, divisor))

        out=self.alloc_BV(len(divident))

        return self.create_wide_MUX([divident, diff], [cmp_res]), cmp_res

    def divider(self, divident, divisor):
        assert len(divident)==len(divisor)
        BITS=len(divisor)

        wide_divisor=self.shift_left([self.const_false]*BITS+divisor, BITS-1)
        quotient=[]
        for b in range(BITS):
            enable=self.NOT(self.OR_list(wide_divisor[:BITS]))
            divident, q_bit=self.div_blk(enable, divident, wide_divisor[BITS:])
            quotient.append(q_bit)
            wide_divisor=self.shift_right_1(wide_divisor)

        # remainder is left in divident:
        return quotient, divident

    def fetch_next_solution(self):
        negated_solution=[]
        for v in range(1, self.last_var):
            negated_solution.append(self.neg_if(self.get_var_from_solution(str(v)), str(v)))
        self.add_clause(negated_solution)
        return self.solve()

    def count_solutions(self):
        if self.solve()==False:
            return 0

        cnt=1
        while True:
            if self.fetch_next_solution()==False:
                break
            cnt=cnt+1
        return cnt

    def get_all_solutions(self):
        if self.solve()==False:
            return None
        rt=[self.solution]

        while True:
            if self.fetch_next_solution()==False:
                break
            rt.append(self.solution)
        return rt

    def BV_not_zero(self,bv):
        return self.OR_list(bv)

    def BV_zero(self, bv):
        return self.NOT(self.OR_list(bv))

    def get_val_from_solution(self,var):
        return BV_to_number(self.get_BV_from_solution(var))

    def make_distinct_BVs (self, lst):
        assert type(lst)==list
        assert type(lst[0])==list
        for pair in itertools.combinations(lst, r=2):
            self.fix_BV_NEQ(pair[0], pair[1])

"""
to be added:

def mathematica_to_CNF (s, d):
    for k in d.keys():
        s=s.replace(k, d[k])
    s=s.replace("!", "-").replace("||", " ").replace("(", "").replace(")", "")
    s=s.split ("&&")
    return s

def sort_unit(a, b):
    return OR([a,b]), AND(a,b)

def sorting_network_make_ladder(lst):
    if len(lst)==2:
        return list(sort_unit(lst[0], lst[1]))

    tmp=sorting_network_make_ladder(lst[1:]) # lst without head
    first, second=sort_unit(lst[0], tmp[0])
    return [first, second] + tmp[1:]

def sorting_network(lst):
    # simplest possible, bubble sort

    if len(lst)==2:
        return sorting_network_make_ladder(lst)

    tmp=sorting_network_make_ladder(lst)
    return sorting_network(tmp[:-1]) + [tmp[-1]]
"""

