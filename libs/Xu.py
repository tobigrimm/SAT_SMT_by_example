#!/usr/bin/env python3

# my own SAT/CNF library

# dennis(a)yurichev, 2017

# "BV" stands for bitvector

import subprocess, os, itertools
import frolic

# BV=[MSB...LSB]
def BV_to_number(BV):
    # coeff=1, 2^1, 2^2 ... 2^(len(BV)-1)
    coeff=1
    rt=0
    for v in frolic.rvr(BV):
        rt=rt+coeff*v
        coeff=coeff*2
    return rt

# bit order: [MSB..LSB]
# 'size' is desired width of bitvector, in bits:
def n_to_BV (n, size):
    out=[0]*size
    i=0
    for var in frolic.rvr(bin(n)[2:]):
        if var=='1':
            out[i]=1
        else:
            out[i]=0
        i=i+1
    return frolic.rvr(out)

class Xu:

    def __init__(self, maxsat):
        self.last_var=1
        # just list of lines to be written to CNF-file:
        self.CNF=[]
        self.HARD_CLAUSE=10000

        self.maxsat=maxsat

        self.SAT_SOLVER="minisat"
        self.MAXSAT_SOLVER="open-wbo"

        self.remove_CNF_file=True
        #self.remove_CNF_file=False

        # allocate a single variable fixed to False:
        self.const_false=self.create_var()
        self.fix(self.const_false,False)
        # allocate a single variable fixed to True:
        self.const_true=self.create_var()
        self.fix(self.const_true,True)

    def run_sat_solver (self):
        child = subprocess.Popen([self.SAT_SOLVER, self.CNF_fname, "results.txt"], stdout=subprocess.PIPE)
        child.wait()
        # 10 is SAT, 20 is UNSAT
        if child.returncode==20:
            os.remove ("results.txt")
            return None

        if child.returncode!=10:
            print ("(minisat) unknown retcode: ", child.returncode)
            exit(0)

        solution=frolic.read_lines_from_file("results.txt")[1].split(" ")
        # remove last "variable", which is 0
        assert solution[-1]=='0'
        solution=solution[:-1]
        os.remove ("results.txt")

        return solution

    def run_maxsat_solver (self):
        tmp_fname="tmp.out"
        logfile=open(tmp_fname, "w")
        child = subprocess.Popen([self.MAXSAT_SOLVER, self.CNF_fname], stdout=logfile)
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

    def write_CNF(self):
        if self.maxsat==False:
            self.CNF_fname="1.cnf"
        else:
            self.CNF_fname="1.wcnf"

        VARS_TOTAL=self.last_var-1
        f=open(self.CNF_fname, "w")
        if self.maxsat==False:
            f.write ("p cnf "+str(VARS_TOTAL)+" "+str(len(self.CNF))+"\n")
        else:
            f.write ("p wcnf "+str(VARS_TOTAL)+" "+str(len(self.CNF))+" "+str(self.HARD_CLAUSE)+"\n")
        for line in self.CNF:
            f.write(line)
        f.close()

    def create_var(self):
        self.last_var=self.last_var+1
        return str(self.last_var-1)

    def neg(self, v):
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
        if self.maxsat==False:
            self.CNF.append(" ".join(cls) + " 0\n")
        else:
            self.CNF.append(str(self.HARD_CLAUSE) + " " + " ".join(cls) + " 0\n")

    def add_soft_clause(self, cls, weight):
        assert self.maxsat==True
        self.CNF.append(str(weight) + " " + " ".join(cls) + " 0\n")

    def AND_Tseitin(self, v1, v2, out):
        self.add_clause([self.neg(v1), self.neg(v2), out])
        self.add_clause([v1, self.neg(out)])
        self.add_clause([v2, self.neg(out)])
    
    def AND(self,v1, v2):
        out=self.create_var()
        self.AND_Tseitin(v1, v2, out)
        return out
    
    def AND_list(l):
        assert(len(l)>=2)
        if len(l)==2:
            return AND(l[0], l[1])
        return AND(l[0], AND_list(l[1:]))

    def BV_AND(self, x,y):
        rt=[]
        for pair in zip(x, y):
            rt.append(self.AND(pair[0],pair[1]))
        return rt
    
    # vals=list
    # as in Tseitin transformations.
    def OR(self, vals):
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
    
    def fix(self, var, b):
        if b==True or b==1:
            self.add_clause([var])
        else:
            self.add_clause([self.neg(var)])
    
    # BV is a list of True/False/0/1
    def fix_BV(self, _vars, BV):
        assert len(_vars)==len(BV)
        for var, _bool in zip(_vars, BV):
            self.fix (var, _bool)

    def get_var_from_solution(self, var):
        # 1 if var is present in solution, 0 if present in negated form:
        if var in self.solution:
            return 1
        if "-"+var in self.solution:
            return 0
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
    
    def EQ(self, x, y):
        return self.NOT(self.XOR(x,y))
    
    def NEQ(self, x, y):
        return self.XOR(x,y)

    # naive/pairwise encoding   
    def AtMost1(self, lst):
        for pair in itertools.combinations(lst, r=2):
            self.add_clause([self.neg(pair[0]), self.neg(pair[1])])
        
    def POPCNT1(self, lst):
        self.AtMost1(lst)
        self.OR_always(lst)
    
    # Hamming distance between two bitvectors is 1
    # i.e., two bitvectors differ in only one bit.
    def hamming1(self,l1, l2):
        self.add_comment("hamming1")
        assert len(l1)==len(l2)
        XORed=self.BV_XOR(l1, l2)
        self.POPCNT1(XORed)
    
    # bitvectors must be different.
    def fix_BV_NEQ(self, l1, l2):
        assert len(l1)==len(l2)
        self.add_comment("fix_BV_NEQ")
        t=[self.XOR(l1[i], l2[i]) for i in range(len(l1))]
        self.fix(self.OR(t), True)

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
        inputs=frolic.rvr(list(zip(X,Y)))
        carry=self.const_false
        sums=[]
        for pair in inputs:
            # "carry" variable is replaced at each iteration.
            # so it is used in the each FA() call from the previous FA() call.
            s, carry = self.FA(pair[0], pair[1], carry)
            sums.append(s)
        return frolic.rvr(sums), carry

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
        for Y_bit in frolic.rvr(Y):
            s, carry = self.adder(self.mult_by_bit(X, Y_bit), prev)
            out.append(s[-1])
            prev=[carry] + s[:-1]
    
        return prev + frolic.rvr(out)

    def NEG(self, x):
        # invert all bits
        tmp=self.BV_NOT(x)
        # add 1
        one=self.alloc_BV(len(tmp))
        self.fix_BV(one,n_to_BV(1, len(tmp)))
        return self.adder(tmp, one)[0]
    
    def shift_left_1 (self, x):
        return x[1:]+[self.const_false] 
    
