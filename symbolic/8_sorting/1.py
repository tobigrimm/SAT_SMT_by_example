#!/usr/bin/env python
class Expr:
    def __init__(self,s,i):
        self.s=s
        self.i=i
    
    def __str__(self):
        # return both symbolic and integer:
        return self.s+" (" + str(self.i)+")"
   
    def __le__(self, other):
        # compare only integer parts:
        return self.i <= other.i

# copypasted from http://rosettacode.org/wiki/Sorting_algorithms/Merge_sort#Python
def merge(left, right):
    result = []
    left_idx, right_idx = 0, 0
    while left_idx < len(left) and right_idx < len(right):
        # change the direction of this comparison to change the direction of the sort
        if left[left_idx] <= right[right_idx]:
            result.append(left[left_idx])
            left_idx += 1
        else:
            result.append(right[right_idx])
            right_idx += 1
 
    if left_idx < len(left):
        result.extend(left[left_idx:])
    if right_idx < len(right):
        result.extend(right[right_idx:])
    return result

def tabs (t):
    return "\t"*t

def merge_sort(m, indent=0):
    print tabs(indent)+"merge_sort() begin. input:"
    for i in m:
        print tabs(indent)+str(i)

    if len(m) <= 1:
        print tabs(indent)+"merge_sort() end. returning single element"
        return m

    middle = len(m) // 2
    left = m[:middle]
    right = m[middle:]
 
    left = merge_sort(left, indent+1)
    right = merge_sort(right, indent+1)
    rt=list(merge(left, right))
    print tabs(indent)+"merge_sort() end. returning:"
    for i in rt:
        print tabs(indent)+str(i)
    return rt

# input buffer has both symbolic and numerical values:
input=[Expr("input1",22), Expr("input2",7), Expr("input3",2), Expr("input4",1), Expr("input5",8), Expr("input6",4)]
merge_sort(input)

