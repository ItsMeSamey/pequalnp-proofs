"""Exact bounded-depth search on the ordered four-probe boundary."""
from itertools import permutations,combinations
from check_ordered_probe_and import cycle,visit
P=list(permutations(range(6)))
idx={p:i for i,p in enumerate(P)}
rot=[]
for c in combinations(range(6),3):
    for t in (c,c[::-1]):
        q=list(range(6)); cycle(q,list(t)); rot.append(q)
step=[[idx[tuple(p[i] for i in q)] for p in P] for q in rot]
S=[]
for m in range(16):
    p=list(range(6))
    for b in (0,1):
        cycle(p,[b]+[i+2 for i in range(4) if m>>i&1==b])
    S.append(p)
target=sum(1<<m for m in range(16) if m&5!=5 and m&10!=10)
def search():
    for a,b in combinations(range(6),2):
        obs=[sum(1<<m for m,s in enumerate(S) if visit([p[i] for i in s],a,b)) for p in P]
        good={i for i,v in enumerate(obs) if v&~target==0}
        def grow(states,trace):
            cover=0
            for i in states:cover|=obs[i]
            if cover==target:return trace
            if len(trace)==4:return
            for k,row in enumerate(step):
                new=states|{row[i] for i in states}
                if new!=states and new<=good:
                    ans=grow(new,trace+[k])
                    if ans:return ans
        for i in sorted(good):
            res=grow({i},[i])
            if res:
                print("pair",a,b,"baseline",P[i],"rotations",[rot[k] for k in res[1:]])
                return
    print('none at depth three')
if __name__=='__main__':search()
