"""Enumerate only residual KW orientation capacities, not monotone circuits."""
from itertools import combinations,product
from collections import Counter
pts=[i for i in range(1,8) if i!=1]
ls=[j for j in range(1,8) if j!=2]
E=tuple((i,6+j) for i,p in enumerate(pts) for j,l in enumerate(ls) if not (p&l).bit_count()%2)
def small(R):return [set(t) for k in range(3) for t in combinations(R,k)]
negs=[a|b for a,b in product(small(range(6)),small(range(6,12))) if not any(i in a and j in b for i,j in E)]
M=[s for s in negs if not any(s<t for t in negs)]
assert len(M)==21
N=[{j if i==k else i for i,j in E if k in (i,j)} for k in range(12)]
coldsets=[set(s) for s in combinations(range(12),5) if not any(set(e)<=set(s) for e in E)]
assert len(coldsets)==16
cert={e:{t for t,m in enumerate(M) if (N[e[0]]|N[e[1]])-set(e)<=m} for e in E}
assert all(len(w)==1 for w in cert.values())
def orientable(edges,caps):
    deg=Counter(v for e in edges for v in e)
    bound=[caps[v]-1 if deg[v]>caps[v] else deg[v] for v in range(12)]
    def visit(i):
        if i==len(edges):return True
        for v in edges[i]:
            if bound[v]>0:
                bound[v]-=1
                if visit(i+1):return True
                bound[v]+=1
        return False
    return visit(0)
for omissions in (0,1,2):
    cases=0
    for missing in combinations(range(len(M)),omissions):
        good=[e for e in E if cert[e]-set(missing)]
        for C in coldsets:
            caps=[1 if v in C else 2 for v in range(12)]
            eligible=[e for e in E if not C&set(e) and all(len(N[v]&C)<2 for v in e)]
            assert all(len(N[c]-C)>=2 for c in C)
            assert len(eligible)<=1
            for loss in [None]+eligible:
                sc=caps[:]
                if loss:
                    for v in loss:sc[v]=1
                assert not orientable([e for e in good if e!=loss],sc)
                cases+=1
    print(omissions,cases,'infeasible orientation systems')
