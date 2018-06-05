#!/usr/bin/env python

from z3 import *

s=Optimize()

libA=Int('libA')
# libA's version is 1..5 or 999 (which means library will not be installed):
s.add(Or(And(libA>=1, libA<=5),libA==999))

libB=Int('libB')
# libB's version is 1, 4, 5 or 999:
s.add(Or(libB==1, libB==4, libB==5, libB==999))

libC=Int('libC')
# libC's version is 10, 11, 14 or 999:
s.add(Or(libC==10, libC==11, libC==14, libC==999))

# libC is dependent on libA
# libC v10 is dependent on libA v1..3, but not newer
# libC v11 requires at least libA v3
# libC v14 requires at least libA v5
s.add(If(libC==10, And(libA>=1, libA<=3), True))
s.add(If(libC==11, libA>=3, True))
s.add(If(libC==14, libA>=5, True))

libD=Int('libD')
# libD's version is 1..10
s.add(Or(And(libD>=1, libD<=10),libD==999))

programA=Int('programA')
# programA came as v1 or v2:
s.add(Or(programA==1, programA==2))

# programA is dependent on libA, libB and libC
# programA v1 requires libA v2 (only this version), libB v4 or v5, libC v10:
s.add(If(programA==1, And(libA==2, Or(libB==4, libB==5), libC==10), True))
# programA v2 requires these libraries: libA v3, libB v5, libC v11
s.add(If(programA==2, And(libA==3, libB==5, libC==11), True))

programB=Int('programB')
# programB came as v7 or v8:
s.add(Or(programB==7, programB==8))

# programB v7 requires libA at least v2 and libC at least v10:
s.add(If(programB==7, And(libA>=2, libC>=10), True))
# programB v8 requires libA at least v6 and libC at least v11:
s.add(If(programB==8, And(libA>=6, libC>=11), True))

s.add(programA==1)
s.add(programB==7) # change this to 8 to make it unsat

# we want latest libraries' versions.
# if the library is not required, its version is "pulled up" to 999,
# and 999 means the library is not needed to be installed
s.maximize(Sum(libA,libB,libC,libD))

print s.check()
print s.model()

