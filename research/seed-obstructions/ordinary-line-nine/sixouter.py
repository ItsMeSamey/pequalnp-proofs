from edge import *
def guard(s,l):
 o=set(range(7))-{l};arm={i for i in o if s>>i&1}
 Q=[sum(1<<p for p in inside(star) if not(s>>j&1) or points[p]&lc[s]) for j,star in enumerate(ss)]
 hit=[pc[q] for q in Q]
 # six ordinary outputs: the one marked attachment is dropped at most once per
 # target, and two equally coloured companions need only be met separately
 # when both have different colours.
 for j in o:
  labels=o-{j}
  tests=[hit[v] for v in labels]+[hit[w]&hit[v] for v,w in combinations(labels,2) if bool(s>>v&1)!=bool(s>>w&1)]
  assert all(all(m&h for m in pairs[j]) for h in tests)
 # If A contains any ordinary nonarm z, use z for its guard. The other AND
 # guards on the OR-side route all use one resident v.
 assert all(all(m&hit[z]&hit[v] for m in pairs[l]) for z in o-arm for v in o)
 assert all(all(m&hit[v] for m in pairs[l]) for v in o)
for s in range(1,128):
 if s.bit_count()!=2:continue
 for l in range(7):
  if not s>>l&1:guard(s,l)
print('Passed 105 repeated-L choices for the six-ordinary no-AND companion tests.')
triple=0
for s in range(1,128):
 if s.bit_count()!=3:continue
 common=8191
 for k in range(7):
  if s>>k&1:common&=ss[k]
 if not common:continue
 assert not failures(s,s)
 for l in range(7):
  if not s>>l&1:
   guard(s,l);triple+=1
assert triple==24
print('Passed the 24 concurrent-triple choices with repeated L outside the loose mask.')
