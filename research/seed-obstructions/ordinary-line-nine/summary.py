from blocks import evaluate
from noand import main
from edge import *
C=Counter(); D=Counter()
for a,b in combinations([s for s in range(1,128) if s.bit_count()>=2],2):
    es=failures(a,b)
    c=(a|b).bit_count()-2+bool(a&b)
    if len(es)==1:
        v=analyze(a,b)
        assert isinstance(v,tuple)
        C[c,main(a,b),v[0]]+=1
    if len(es)==2 and not set(es[0])&set(es[1]):
        D[main(a,b),tuple(evaluate(a,b,g) for g in ([es[0]],[es[1]],es))]+=1
for c in range(2,7):
    print('One missing edge; line cost',c,[(x,y,n) for (k,x,y),n in C.items() if k==c])
print('Two disjoint missing edges:',D)
assert [C[c,'all','all'] for c in range(2,7)]==[105,732,735,336,63]
assert sum(D.values())==D['distinct',('all','all','all')]==105
