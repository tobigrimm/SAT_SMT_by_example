from z3 import *

def char_to_idx(c):
    return ord(c)-ord('A')

def idx_to_char(i):
    return chr(ord('A')+i)

# construct expression in form like:
# 10000000*L+1000000*U+100000*N+10000*C+1000*H+100*E+10*O+N
def list_to_expr(lst):
    coeff=1
    _sum=0
    for var in lst[::-1]:
        _sum=_sum+var*coeff
        coeff=coeff*10
    return _sum

# this table has 10 items, it reflects character for each number:
digits=[Int('digit_%d' % i) for i in range(10)]

# this is "reverse" table, it has value for each letter:
letters=[Int('letter_%d' % i) for i in range(26)]

s=Solver()

# all items in digits[] table must be distinct, because no two letters can share same number:
s.add(Distinct(digits))

# all numbers are in 0..25 range, because each number in this table defines character:
for i in range(10):
    s.add(And(digits[i]>=0,digits[i]<26))

# define "reverse" table.
# letters[i] is 0..9, depending on which digits[] item contains this letter:
for i in range(26):
    s.add(letters[i] == 
        If(digits[0]==i,0,
        If(digits[1]==i,1,
        If(digits[2]==i,2,
        If(digits[3]==i,3,
        If(digits[4]==i,4,
        If(digits[5]==i,5,
        If(digits[6]==i,6,
        If(digits[7]==i,7,
        If(digits[8]==i,8,
        If(digits[9]==i,9,99999999)))))))))))

# the last word is "sum" all the rest are "addends":

words=['APPLE', 'BANANA', 'BREAD', 'CAKE', 'CAVIAR', 'CHEESE', 'CHIPS', 'COFFEE', 'EGGS', 'FISH', 'HONEY', 'JAM', 'JELLY', 'JUICE', 'MILK', 'OATMEAL', 'ORANGE', 'PANCAKE', 'PIZZA', 'STEAK', 'TEA', 'TOMATO', 'WAFFLE', 'LUNCH']

words_total=len(words)

word=[Int('word_%d' % i) for i in range(words_total)]
word_used=[Bool('word_used_%d' % i) for i in range(words_total)]

# last word is always used:
s.add(word_used[words_total-1]==True)

#s.add(word_used[words.index('CAKE')])
s.add(word_used[words.index('EGGS')])

for i in range(words_total):
    # get list of letters for the word:
    lst=[letters[char_to_idx(c)] for c in words[i]]
    # construct expression for letters. it must be equal to the value of the word:
    s.add(word[i]==list_to_expr(lst))
    # if word_used, word's value must be less than 99999999, i.e., all letters are used in the word:
    s.add(If(word_used[i], word[i], 0) < 99999999)

# if word_used, add value of word to the whole expression
expr=[If(word_used[i], word[i], 0) for i in range(words_total-1)]
# sum up all items in expression. sum must be equal to the value of the last word:
s.add(sum(expr)==word[-1])

print s.check()
m=s.model()
#print m

for i in range(words_total):
    # if word_used, print it:
    if str(m[word_used[i]])=="True" or i+1==words_total:
        print words[i]

for i in range(26):
    # it letter is used, print it:
    if m[letters[i]].as_long()!=99999999:
        print idx_to_char(i), m[letters[i]]

