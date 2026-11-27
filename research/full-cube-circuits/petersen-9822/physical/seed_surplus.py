from pathlib import Path
import re
import networkx as nx
from collections import defaultdict
from itertools import combinations,product
from functools import cache
E=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
@cache
def norm(F):
    a=set(F)
    return tuple(sorted(x for x in a if not any(t!=x and t&x==t for t in a)))
@cache
def pin(F,x,b):return norm(tuple(t&~x if b else t for t in F if b or not(t&x)))
@cache
def mask(F):
    a=0
    for t in F:a|=t
    return a
base=Path('/workspace/pequalnp-proofs/lean/PEqualNP/Outside')
archive=defaultdict(list)
def graph(terms):
    g=nx.Graph()
    for t in terms:
        xy=[i for i in range(t.bit_length()) if t>>i&1]
        if len(xy)==2:g.add_edge(*xy)
    return g
def key(g):
    return tuple(sorted(d for _,d in g.degree()))
for unit in [9752,9825]:
    f=(base/f'L_meta_{unit}.lean').read_text()
    expr=f.split('def graphGoal (m : Nat) : Sig :=',1)[1].split('def ',1)[0]
    gg=[(int(a),int(b)) for a,b in re.findall(r'\(x (\d+) &&& x (\d+)\)',expr)]
    assert len(gg)==(14 if unit==9752 else 13)
    for m,lo in re.findall(r'^theorem h\d+_\d+ : Face true (\d+) (\d+)',f,re.M):
        m=int(m);lo=int(lo)
        g=graph([(1<<a)|(1<<b) for a,b in gg if m>>a&m>>b&1])
        if g.number_of_edges():archive[key(g)].append((g,lo,unit,m))
@cache
def seed(F):
    # Extra pure OR literals are independent and cost one binary gate each.
    es=tuple(t for t in F if t.bit_count()==2)
    if not es:return 0
    G=graph(es)
    best=max((lo for g,lo,unit,m in archive[key(G)] if nx.is_isomorphic(g,G)),default=0)
    return max(0,best-(G.number_of_nodes()-1))
@cache
def score(F):
    A=mask(F)
    xs=[1<<i for i in range(A.bit_length()) if A>>i&1]
    if len(xs)<3:return 0
    best=len(xs)*2
    for x,y in combinations(xs,2):
        # If both raw inputs enter the rest exclusively through this binary gate,
        # at most two joint cofactors exist. Equal pinning contracts that module.
        Fxy=[[pin(pin(F,x,a),y,b) for b in (0,1)] for a in (0,1)]
        if len({u for row in Fxy for u in row})<=2:
            merged=norm(tuple(t&~y|x if t&y else t for t in F))
            best=min(best,score(merged))
        # For a signed canalizing gate select each possible pair of controlling bits.
        # If the counterpart is essential at a controlling bit, it needs another use.
        for cx,cy in product((0,1),repeat=2):
            rx=bool(mask(pin(F,y,cy))&x)
            ry=bool(mask(pin(F,x,cx))&y)
            if rx and ry:
                cost=2+max(score(u) for row in Fxy for u in row)
            elif rx or ry:
                z=x if rx else y
                cost=1+max(score(pin(F,z,b)) for b in (0,1))
            else:
                cost=1+min(max(score(pin(F,z,b)) for b in (0,1)) for z in (x,y))
            def binary(G):
                return max(0,mask(G).bit_count()-1)+score(G)
            d1=1+int(rx)
            d2=1+int(ry)
            # Boolean desk first-gate deletion lemma: controlling assignment
            # deletes one more downstream gate than the lower raw-use count.
            extra=max(binary(pin(F,z,b))+debit+int(b==ctrl) for z,ctrl,debit in ((x,cx,d1),(y,cy,d2)) for b in (0,1))-(len(xs)-1)
            best=min(max(cost,extra),best)
        if best==0:return seed(F)
    return max(best,seed(F))
F=norm(tuple((1<<i)|(1<<j) for i,j in E))
print(score(F),score.cache_info(),flush=True)
print('prior signed declarations',sum(map(len,archive.values())),'full seed',seed(F))
for i in range(10):
 print(i,[(score(g)+max(0,mask(g).bit_count()-1),seed(g)) for g in [pin(F,1<<i,b) for b in (0,1)]])
