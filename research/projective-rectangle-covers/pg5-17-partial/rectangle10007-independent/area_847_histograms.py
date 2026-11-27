from fractions import Fraction as Q
from itertools import combinations

cost=[Q((25+i)**2,625+50*i+121*i*i) for i in range(5)]
rank_survivors=[]
large_survivors=[]
odd_survivors=[]
# Stars and bars enumerates the five nonnegative parts of 31.
for bars in combinations(range(35), 4):
    endpoints=(-1,*bars,35)
    c=tuple(b-a-1 for a,b in zip(endpoints,endpoints[1:]))
    assert sum(c)==31
    if sum(i*n for i,n in enumerate(c))!=72:
        continue
    if sum(f*n for f,n in zip(cost,c))>17:
        continue
    rank_survivors.append(c)
    if c[3]+c[4]<14:continue
    large_survivors.append(c)
    if c[1]+c[3]>=17:odd_survivors.append(c)
print(len(rank_survivors),len(large_survivors),odd_survivors)
assert odd_survivors==[(4,0,9,18,0)]
