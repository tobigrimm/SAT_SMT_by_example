from z3 import *
import itertools

# RAM, storage, both in GB
servers=[(2, 100),
(4, 800),
(4, 1000),
(16, 8000),
(8, 3000),
(16, 6000),
(16, 4000),
(32, 2000),
(8, 1000),
(16, 10000),
(8, 1000)]

# RAM, storage
vms=[(1, 100),
(16, 900),
(4, 710),
(2, 800),
(4, 7000),
(8, 4000),
(2, 800),
(4, 2500),
(16, 450),
(16, 3700),
(12, 1300)]

vms_total=len(vms)

VM_RAM_t=sum(map(lambda x: x[0], vms))
VM_storage_t=sum(map(lambda x: x[1], vms))

print "RAM total we need", VM_RAM_t
print "storage total we need", VM_storage_t

def try_to_fit_into_servers(servers_to_be_used):
    t=len(servers_to_be_used)
    # for each server:
    RAM_allocated=[Int('srv%d_RAM_allocated' % i) for i in range(t)]
    storage_allocated=[Int('srv%d_storage_allocated' % i) for i in range(t)]
    # which server this VM occupies?
    VM_in_srv=[Int('VM%d_in_srv' % i) for i in range(vms_total)]

    # how much RAM/storage we have in picked servers, total?
    RAM_t=0
    storage_t=0
    for i in range(t):
        RAM_t=RAM_t+servers[servers_to_be_used[i]][0]
        storage_t=storage_t+servers[servers_to_be_used[i]][1]
    # skip if the sum of RAM/storage in picked servers is too small:
    if VM_RAM_t>RAM_t or VM_storage_t>storage_t:
        return

    print "trying to fit VMs into servers:", servers_to_be_used,

    s=Solver()

    # all VMs must occupy some server:
    for i in range(vms_total):
        s.add(And(VM_in_srv[i]>=0, VM_in_srv[i]<t))

    for i in range(t):
        """
        here we generate expression like:

        If(VM0_in_srv == 3, 1, 0) +
        If(VM1_in_srv == 3, 16, 0) +
        If(VM2_in_srv == 3, 4, 0) +
        If(VM3_in_srv == 3, 2, 0) +
        If(VM4_in_srv == 3, 4, 0) +
        If(VM5_in_srv == 3, 8, 0) +
        If(VM6_in_srv == 3, 2, 0) +
        If(VM7_in_srv == 3, 4, 0) +
        If(VM8_in_srv == 3, 16, 0) +
        If(VM9_in_srv == 3, 16, 0) +
        If(VM10_in_srv == 3, 12, 0)

        ... in plain English - if a VM is in THIS server, add a number (RAM/storage required by this VM) to the final sum

        """

        # RAM
        s.add(RAM_allocated[i]==Sum([If(VM_in_srv[v]==i, vms[v][0], 0) for v in range(vms_total)]))
        # storage
        s.add(storage_allocated[i]==Sum([If(VM_in_srv[v]==i, vms[v][1], 0) for v in range(vms_total)]))

        # ... but sum of all RAM/storage occupied in each server must be lower than what we have in the server:
        s.add(And(RAM_allocated[i]>=0, RAM_allocated[i]<=servers[servers_to_be_used[i]][0]))
        s.add(And(storage_allocated[i]>=0, storage_allocated[i]<=servers[servers_to_be_used[i]][1]))
    if s.check()==sat:
        print "sat"
        print "* solution (%d servers):" % t
        m=s.model()

        for i in range(t):
            print "srv%d (total=%d/%d):" % (servers_to_be_used[i], servers[servers_to_be_used[i]][0], servers[servers_to_be_used[i]][1]),
            for v in range(vms_total):
                if m[VM_in_srv[v]].as_long()==i:
                    print "VM%d (%d/%d)" % (v, vms[v][0], vms[v][1]),
            print "allocated on srv=%d/%d" % (m[RAM_allocated[i]].as_long(), m[storage_allocated[i]].as_long()),
            print "free on srv=%d/%d" % (servers[servers_to_be_used[i]][0] - m[RAM_allocated[i]].as_long(), servers[servers_to_be_used[i]][1] - m[storage_allocated[i]].as_long()),
            print ""
        print "total in all servers=%d/%d" % (RAM_t, storage_t)
        print "allocated on all servers=%d%%/%d%%" % ((float(VM_RAM_t)/float(RAM_t))*100, (float(VM_storage_t)/float(storage_t))*100)
        print ""
        return True
    else:
        print "unsat"
        return False

# how many servers we need? start with 2:
found_solution=False
for servers_to_pick in range(2, len(servers)+1):

    # we use Python itertools to find all combinations
    # in other words, pick $servers_to_pick$ servers from all servers, and enumerate all possible ways to choose from them.
    # see also: https://en.wikipedia.org/wiki/Combination
    for servers_to_be_used in itertools.combinations(range(len(servers)), r=servers_to_pick):
        if try_to_fit_into_servers(servers_to_be_used):
            found_solution=True
    # after we've got some solutions for $servers_to_pick$, stop:
    if found_solution:
        break

