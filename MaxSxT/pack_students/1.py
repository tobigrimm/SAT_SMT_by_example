import SAT_lib

s=SAT_lib.SAT_lib(maxsat=True)

STUDENTS=15
CEILING_LOG2_STUDENTS=4 # 4 bits to hold a number in 0..14 range

POSSIBLE_INTERESTS=8

# interests/hobbies for each student. 8 are possible:
interests=[
0b10000100,
0b01000001,
0b00000010,
0b01000001,
0b00001001,
0b00101000,
0b00000100,
0b00000011,
0b01000000,
0b00000100,
0b10000001,
0b00001000,
0b00000010,
0b01000001,
0b01000010,
0] # dummy variable, to pad the list to 16 elements

# each variable is "grounded" to the bitmask from interests[]:
interests_vars=[s.alloc_BV(POSSIBLE_INTERESTS) for i in range(2**CEILING_LOG2_STUDENTS)]
for st in range(2**CEILING_LOG2_STUDENTS):
    s.fix_BV(interests_vars[st], SAT_lib.n_to_BV(interests[st], POSSIBLE_INTERESTS))

# where each student is located after permutation:
students_positions=[s.alloc_BV(CEILING_LOG2_STUDENTS) for i in range(2**CEILING_LOG2_STUDENTS)]

# permutation. all positions are distinct, of course:
s.make_distinct_BVs (students_positions)

# connect interests of each student to permuted version
# use multiplexer...
interests_of_student_in_position={}
for st in range(2**CEILING_LOG2_STUDENTS):
    interests_of_student_in_position[st]=s.create_wide_MUX (interests_vars, students_positions[st])

# divide result of permutation by triplets
# we want as many similar bits in interests[] between all 3 students, as possible:
for group in range(STUDENTS/3):
    i1=interests_of_student_in_position[group*3]
    i2=interests_of_student_in_position[group*3+1]
    i3=interests_of_student_in_position[group*3+2]
    s.fix_soft_always_true_all_bits_in_BV(s.BV_AND(i1, i2), weight=1)
    s.fix_soft_always_true_all_bits_in_BV(s.BV_AND(i1, i3), weight=1)
    s.fix_soft_always_true_all_bits_in_BV(s.BV_AND(i2, i3), weight=1)

assert s.solve()

def POPCNT(v):
    rt=0
    for i in range(POSSIBLE_INTERESTS):
        if ((v>>i)&1)==1:
            rt=rt+1
    return rt

total_in_all_groups=0

# print solution:
for group in range(STUDENTS/3):
    print "* group", group
    st1=SAT_lib.BV_to_number(s.get_BV_from_solution(students_positions[group*3]))
    st2=SAT_lib.BV_to_number(s.get_BV_from_solution(students_positions[group*3+1]))
    st3=SAT_lib.BV_to_number(s.get_BV_from_solution(students_positions[group*3+2]))

    print "students:", st1, st2, st3

    c12=POPCNT(interests[st1]&interests[st2])
    c13=POPCNT(interests[st1]&interests[st3])
    c23=POPCNT(interests[st2]&interests[st3])

    print "common interests between 1 and 2:", c12
    print "common interests between 1 and 3:", c13
    print "common interests between 2 and 3:", c23

    total=c12+c13+c23
    print "total=", total
    total_in_all_groups=total_in_all_groups+total

print "* total in all groups=", total_in_all_groups

