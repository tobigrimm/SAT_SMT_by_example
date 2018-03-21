from z3 import *

# the city matrix has been copypasted from https://developers.google.com/optimization/routing/tsp/tsp
matrix=[
  [   0, 2451,  713, 1018, 1631, 1374, 2408,  213, 2571,  875, 1420, 2145, 1972], # New York
  [2451,    0, 1745, 1524,  831, 1240,  959, 2596,  403, 1589, 1374,  357,  579], # Los Angeles
  [ 713, 1745,    0,  355,  920,  803, 1737,  851, 1858,  262,  940, 1453, 1260], # Chicago
  [1018, 1524,  355,    0,  700,  862, 1395, 1123, 1584,  466, 1056, 1280,  987], # Minneapolis
  [1631,  831,  920,  700,    0,  663, 1021, 1769,  949,  796,  879,  586,  371], # Denver
  [1374, 1240,  803,  862,  663,    0, 1681, 1551, 1765,  547,  225,  887,  999], # Dallas
  [2408,  959, 1737, 1395, 1021, 1681,    0, 2493,  678, 1724, 1891, 1114,  701], # Seattle
  [ 213, 2596,  851, 1123, 1769, 1551, 2493,    0, 2699, 1038, 1605, 2300, 2099], # Boston
  [2571,  403, 1858, 1584,  949, 1765,  678, 2699,    0, 1744, 1645,  653,  600], # San Francisco
  [ 875, 1589,  262,  466,  796,  547, 1724, 1038, 1744,    0,  679, 1272, 1162], # St. Louis
  [1420, 1374,  940, 1056,  879,  225, 1891, 1605, 1645,  679,    0, 1017, 1200], # Houston
  [2145,  357, 1453, 1280,  586,  887, 1114, 2300,  653, 1272, 1017,    0,  504], # Phoenix
  [1972,  579, 1260,  987,  371,  999,  701, 2099,  600, 1162,  1200,  504,   0]] # Salt Lake City

# 13 cities:
city_names = ["New York", "Los Angeles", "Chicago",
              "Minneapolis", "Denver", "Dallas", "Seattle", "Boston", "San Francisco",
              "St. Louis", "Houston", "Phoenix", "Salt Lake City"]

# unfortunately, we use only first 6 cities:
cities_t=6
#cities_t=len(city_names)

"""
this function generates expression like:

If(And(route_5 == 5, route_0 == 5),
   0,
   If(And(route_5 == 5, route_0 == 4),
      663,
      If(And(route_5 == 5, route_0 == 3),
         862,
         If(And(route_5 == 5, route_0 == 2),
            803,
            If(And(route_5 == 5, route_0 == 1),
               1240,
...

so it's like switch()
"""

def distance_fn(c1, c2):
    t=9999999 # default value
    for i in range(cities_t):
        for j in range(cities_t):
            t=If(And(c1==i, c2==j), matrix[i][j], t)
    #print t
    return t

s=Optimize()

# which city is visited on each step of route?
route=[Int('route_%d' % i) for i in range(cities_t)]
# what distance between the current city and the next in route[]?
distance=[Int('distance_%d' % i) for i in range(cities_t)]

# all ints in route[] must be in [0..cities_t) range:
for r in route:
    s.add(r>=0, r<cities_t)

# no city may be visited twice:
s.add(Distinct(route))

for i in range(cities_t):
    s.add(distance[i]==distance_fn(route[i], route[(i+1) % cities_t]))

distance_total=Int('distance_total')

s.add(distance_total==Sum(distance))

# minimize total distance:
#s.minimize(distance_total)
# or maximize:
s.maximize(distance_total)

print s.check()
m=s.model()
#print m
for i in range(cities_t):
    print "%s (%d mi to the next city) ->" % (city_names[m[route[i]].as_long()], m[distance[i]].as_long())

print "distance_total=", m[distance_total], "mi"

