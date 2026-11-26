"""Check the finite lemmas for two extra line leaves in a read-once tree."""
from collections import Counter
from itertools import combinations, combinations_with_replacement, product
from pathlib import Path
import sys

source = Path(sys.argv[1]) if len(sys.argv) > 1 else Path(__file__).resolve().parent.parent
sys.path.insert(0, str(source.resolve()))
from verify_mixed import coords, target

stars = [sum(1 << ((6+j+d) % 13) for d in (0,1,3,9)) for j in range(7)]
negatives = [coords(i) for i in range(676) if not target >> i & 1]

def companions(residents, exceptions, patterns, t):
    active = [i for i,group in enumerate(residents) if t in group and exceptions[i] != t]
    if not active:
        return True
    return any(u != t and all(u in residents[i] and patterns[u][i] <= patterns[t][i] for i in active)
               for u in range(len(patterns)))

# Relabel inner members by (inner bit,outer bit) and exterior members by outer bit.
classes = [(True,a,b) for a,b in product(range(2),repeat=2)] + [(False,0,b) for b in range(2)]
cases = 0
for n in range(1,8):
    for c in combinations_with_replacement(classes,n):
        inner = [j for j,(inside,_,_) in enumerate(c) if inside]
        if not inner:
            continue
        outer = list(range(n))
        patterns = [(a,b) for _,a,b in c]
        assert any(all(companions((inner,outer), (a,b), patterns,t) for t in outer)
                   for a,b in product([-1,*inner],[-1,*outer]))
        cases += 1
print('Nested guard roles checked:',cases)

for n in range(1,8):
    for types in combinations_with_replacement(range(4),n):
        minimal_unique = [i for i,p in enumerate(types) if not any(i!=j and q&~p==0 for j,q in enumerate(types))]
        assert len(minimal_unique)<=2
print('One attachment with two extra leaves has at most two unmatched residents.')
for e in range(12):
    assert min(e,8-e)<=4

count=0
for t,star in enumerate(stars):
    for i,j in combinations_with_replacement([k for k in range(7) if k!=t],2):
        witness=[n for n,l in negatives if l>>t&1 and n&stars[i] and n&stars[j]]
        for x,y in combinations([k for k in range(13) if not star>>k&1],2):
            pair=1<<x|1<<y
            assert any(not pair&~n for n in witness)
            count+=1
assert count==5292
print('Raw private-guard witnesses:',count)
# The zero-line cofactor with both loose bits at one rejects if some negative
# dominates that point and has both loose bits true at its line assignment.
indicators=[[l for n,l in negatives if n&(1<<i)] for i in range(13)]
def good(a,b):
    return all(any(l&a and l&b for l in masks) for masks in indicators)
stats=Counter()
for a,b in combinations_with_replacement(range(1,128),2):
    if good(a,b):
        stats[a.bit_count(),b.bit_count()]+=1
n=sum(stats.values())
assert n==4371
print('Jointly pinnable nonempty unordered line-mask pairs:',n,'of 8128.')
