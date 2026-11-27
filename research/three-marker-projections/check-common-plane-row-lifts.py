from itertools import combinations
from functools import reduce
from operator import xor

K=[2,11,4,8,3,5,9,12,7,13,10]
t=1165
B=[449,1666,1348,712,848,2016]
o=27569
P={6,42,44}
H=[34,25,59]
def bit(x):return x.bit_count()%2
def vs(B):
    s=[0]
    for b in B:s.extend([x^b for x in s])
    return s
Z=vs(B)
names={v:x for x,v in enumerate(Z)}
assert len(names)==64
def private(word):
    return reduce(xor,(key for i,key in enumerate(K) if word>>i&1),0)
assert set(Z)=={v for v in range(1<<len(K)) if private(v)==0 and not bit(v&t)}
def omega(x,y):
    return sum(((o>>i)&1)*(((x>>a&y>>b)^(x>>b&y>>a))&1)
               for i,(a,b) in enumerate(combinations(range(len(B)),2)))%2
def proj(x):return sum(omega(x,1<<j)<<j for j in range(len(B)))
assert len({proj(x) for x in range(64)})==16
rows=[sum(bit(k&g)<<i for i,k in enumerate(K)) for g in range(16)]
def hits(tag,h):
    all_values=[]
    result=[]
    for g,row in enumerate(rows):
        ok=[(x,v) for x,v in enumerate(Z) if not (v&(row^tag)) and not bit(h&v)]
        for (x,v),(y,w) in combinations(ok,2):
            if omega(x,y):
                all_values.append((g,v,w))
                if {proj(x),proj(y),proj(x^y)}==P:
                    result.append((g,v,w))
    return all_values,result
assert not hits(t,0)[0]
active=[x for x,z in enumerate(Z) if any(not z&(t^r) for r in rows)]
aggregate={0}
for x in active:aggregate.update({v^x for v in list(aggregate)})
assert len(aggregate)==64
assert all(not bit(h&x) for h in H for x in range(64) if proj(x) in P)
assert H[0]^H[1]==H[2]
assert {h for h in {proj(x) for x in range(64)} if all(not bit(h&x) for x in range(64) if proj(x) in P)}=={0,*H}
for hv in H:
    h=next(q for q in range(1<<len(K)) if all(bit(q&v)==(hv>>j&1) for j,v in enumerate(B)))
    u=hits(t^h,h)[1][0];v=hits(h,h^t)[1][0]
    print(hv,h,'t+h',u,'h',v)
