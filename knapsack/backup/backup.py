from z3 import *
import itertools

storages=[700, 30, 100, 800, 100, 800, 300, 150, 60, 500, 1000]
files=[18, 57, 291, 184, 167, 496, 45, 368, 144, 428, 15, 100, 999]

files_n=len(files)
files_t=sum(files)

print "storage total we need", files_t

def try_to_fit_into_storages(storages_to_be_used):
    t=len(storages_to_be_used)
    # for each server:
    storage_occupied=[Int('storage%d_occupied' % i) for i in range(t)]
    # which storage the file occupies?
    file_in_storage=[Int('file%d_in_storage' % i) for i in range(files_n)]

    # how much storage we have in picked storages, total?
    storage_t=0
    for i in range(t):
        storage_t=storage_t+storages[storages_to_be_used[i]]
    # skip if the sum of storage in picked storages is too small:
    if files_t > storage_t:
        return

    print "trying to fit all the files into storages:", storages_to_be_used,

    s=Solver()

    # all files must occupy some storage:
    for i in range(files_n):
        s.add(And(file_in_storage[i]>=0, file_in_storage[i]<t))

    for i in range(t):
        """
        here we generate expression like:

        If(file1_in_storage == 4, 57, 0) +
        If(file1_in_storage == 4, 291, 0) +
        If(file1_in_storage == 4, 184, 0) +
        If(file1_in_storage == 4, 167, 0) +
        If(file1_in_storage == 4, 496, 0) +
        If(file1_in_storage == 4, 45, 0) +
        If(file1_in_storage == 4, 368, 0) +
        If(file1_in_storage == 4, 144, 0) +
        If(file1_in_storage == 4, 428, 0) +
        If(file1_in_storage == 4, 15, 0)

        ... in plain English - if a file is in storage, add its size to the final sum

        """

        s.add(storage_occupied[i]==Sum([If(file_in_storage[f]==i, files[f], 0) for f in range(files_n)]))

        # ... but sum of all files in each storage must be lower than what we have in the storage:
        s.add(And(storage_occupied[i]>=0, storage_occupied[i]<=storages[storages_to_be_used[i]]))
    if s.check()==sat:
        print "sat"
        print "* solution (%d storages):" % t
        m=s.model()
        #print m
        for i in range(t):
            print "storage%d (total=%d):" % (storages_to_be_used[i], storages[storages_to_be_used[i]])
            for f in range(files_n):
                if m[file_in_storage[f]].as_long()==i:
                    print "    file%d (%d)" % (f, files[f])
            print "allocated on storage=%d" % (m[storage_occupied[i]].as_long()),
            print "free on storage=%d" % (storages[storages_to_be_used[i]] - m[storage_occupied[i]].as_long())
        print "total in all storages=%d" % storage_t
        print "allocated on all storages=%d%%" % ((float(files_t)/float(storage_t))*100)
        print ""
        return True
    else:
        print "unsat"
        return False

# how many storages we need? start with 2:
found_solution=False
for storages_to_pick in range(2, len(storages)+1):

    # we use Python itertools to find all combinations
    # in other words, pick $storages_to_pick$ storages from all storages, and enumerate all possible ways to choose from them.
    # see also: https://en.wikipedia.org/wiki/Combination
    for storages_to_be_used in itertools.combinations(range(len(storages)), r=storages_to_pick):
        # for some reasons, we may want to always use storage0
        # skip all sets, where no storage0 present:
        if 0 not in storages_to_be_used:
            continue
        if try_to_fit_into_storages(storages_to_be_used):
            found_solution=True
    # after we've got some solutions for $storages_to_pick$, stop:
    if found_solution:
        break

