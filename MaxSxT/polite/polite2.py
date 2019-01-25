from z3 import *

# we don't use coins for simplicity, but it's not a problem to add them

# banknotes in cash register
cash_register_1=1
cash_register_3=0
cash_register_5=2
cash_register_10=2
cash_register_25=0
cash_register_50=12
cash_register_100=10

# ... in customer's wallet
customer_wallet_1=2
customer_wallet_3=1
customer_wallet_5=1
customer_wallet_10=1
customer_wallet_25=0
customer_wallet_50=15
customer_wallet_100=20

# what customer have to pay
checkout=2135

from_cash_register_1=Int('from_cash_register_1')
from_cash_register_3=Int('from_cash_register_3')
from_cash_register_5=Int('from_cash_register_5')
from_cash_register_10=Int('from_cash_register_10')
from_cash_register_25=Int('from_cash_register_25')
from_cash_register_50=Int('from_cash_register_50')
from_cash_register_100=Int('from_cash_register_100')

from_customer_wallet_1=Int('from_customer_wallet_1')
from_customer_wallet_3=Int('from_customer_wallet_3')
from_customer_wallet_5=Int('from_customer_wallet_5')
from_customer_wallet_10=Int('from_customer_wallet_10')
from_customer_wallet_25=Int('from_customer_wallet_25')
from_customer_wallet_50=Int('from_customer_wallet_50')
from_customer_wallet_100=Int('from_customer_wallet_100')

s=Optimize()

# banknotes pulled from cash_register are limited by 0 and what is defined:
s.add(And(from_cash_register_1 >= 0, from_cash_register_1 <= cash_register_1))
s.add(And(from_cash_register_3 >= 0, from_cash_register_3 <= cash_register_3))
s.add(And(from_cash_register_5 >= 0, from_cash_register_5 <= cash_register_5))
s.add(And(from_cash_register_10 >= 0, from_cash_register_10 <= cash_register_10))
s.add(And(from_cash_register_25 >= 0, from_cash_register_25 <= cash_register_25))
s.add(And(from_cash_register_50 >= 0, from_cash_register_50 <= cash_register_50))
s.add(And(from_cash_register_100 >= 0, from_cash_register_100 <= cash_register_100))

# same for customer's wallet:
s.add(And(from_customer_wallet_1 >= 0, from_customer_wallet_1 <= customer_wallet_1))
s.add(And(from_customer_wallet_3 >= 0, from_customer_wallet_3 <= customer_wallet_3))
s.add(And(from_customer_wallet_5 >= 0, from_customer_wallet_5 <= customer_wallet_5))
s.add(And(from_customer_wallet_10 >= 0, from_customer_wallet_10 <= customer_wallet_10))
s.add(And(from_customer_wallet_25 >= 0, from_customer_wallet_25 <= customer_wallet_25))
s.add(And(from_customer_wallet_50 >= 0, from_customer_wallet_50 <= customer_wallet_50))
s.add(And(from_customer_wallet_100 >= 0, from_customer_wallet_100 <= customer_wallet_100))

from_cash_register=Int('from_cash_register')

# sum:
s.add(from_cash_register==
from_cash_register_1*1 +
from_cash_register_3*3 +
from_cash_register_5*5 +
from_cash_register_10*10 +
from_cash_register_25*25 +
from_cash_register_50*50 +
from_cash_register_100*100)

from_customer=Int('from_customer')

s.add(from_customer==
from_customer_wallet_1*1 +
from_customer_wallet_3*3 +
from_customer_wallet_5*5 +
from_customer_wallet_10*10 +
from_customer_wallet_25*25 +
from_customer_wallet_50*50 +
from_customer_wallet_100*100)

# the main constraint:
s.add(from_customer - checkout == from_cash_register)

value_of_banknotes_from_cash_register=Int('value_of_banknotes_from_cash_register')

# minimize number of all banknotes in transaction:
s.minimize(
from_cash_register_1 + 
from_cash_register_3 + 
from_cash_register_5 + 
from_cash_register_10 + 
from_cash_register_25 + 
from_cash_register_50 + 
from_cash_register_100 +
from_customer_wallet_1 +
from_customer_wallet_3 +
from_customer_wallet_5 +
from_customer_wallet_10 +
from_customer_wallet_25 +
from_customer_wallet_50 +
from_customer_wallet_100)

print s.check()
m=s.model()

print "from_cash_register_1=", m[from_cash_register_1]
print "from_cash_register_3=", m[from_cash_register_3]
print "from_cash_register_5=", m[from_cash_register_5]
print "from_cash_register_10=", m[from_cash_register_10]
print "from_cash_register_25=", m[from_cash_register_25]
print "from_cash_register_50=", m[from_cash_register_50]
print "from_cash_register_100=", m[from_cash_register_100]

print "from_cash_register=", m[from_cash_register]

print ""

print "from_customer_wallet_1=", m[from_customer_wallet_1]
print "from_customer_wallet_3=", m[from_customer_wallet_3]
print "from_customer_wallet_5=", m[from_customer_wallet_5]
print "from_customer_wallet_10=", m[from_customer_wallet_10]
print "from_customer_wallet_25=", m[from_customer_wallet_25]
print "from_customer_wallet_50=", m[from_customer_wallet_50]
print "from_customer_wallet_100=", m[from_customer_wallet_100]

print "from_customer=", m[from_customer]

