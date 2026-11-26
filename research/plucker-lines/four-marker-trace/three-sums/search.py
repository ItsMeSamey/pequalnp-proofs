from random import Random
from itertools import combinations
rng=Random(25274)
def rank(E):
    B={}
    for x in E:
        while x and x.bit_length() in B:x^=B[x.bit_length()]
        if x:B[x.bit_length()]=x
    return len(B)
def three(E):
    n=len(E);r=rank(E)
    for k in range(2,n//2+1):
        for I in combinations(range(n),k):
            J=set(I)
            if rank([E[i] for i in I])+rank([v for i,v in enumerate(E) if i not in J])<r+2:return False
    return True
def assignments(E):
    data=[]
    for c in range(1<<len(E)):
        w=0
        for i,e in enumerate(E):
            if c>>i&1:w^=e
        if w>=4:continue
        for d in range(16):
            D=sum(((e&d).bit_count()%2)<<i for i,e in enumerate(E))
            if not c&D:data.append((w+4*(d&3),c,D))
    return data
def profile(E,ass,k):
    a=[rng.randrange(1<<k) for _ in E];b=[rng.randrange(1<<k) for _ in E]
    def scores(L):
        s=[0]
        for z in L:s += [v^z for v in s]
        return s
    aa,bb=scores(a),scores(b);S=[set() for _ in range(16)]
    for m,c,d in ass:S[m].add(aa[c]^bb[d])
    return a,b,S
def planes():
    out=[(0,1,2,3),(0,4,8,12)]
    for w,d in [(1,2),(2,1),(3,3)]:out.append((0,w,4*d,w+4*d))
    return out
if __name__=='__main__':
    configs=[]
    for n in [7,8,9]:
        for E in combinations(range(4,16),n):
            if three(E):configs.append((E,assignments(E)))
            if sum(len(v[0])==n for v in configs)>=12:break
    print('configs',len(configs),flush=True)
    for it in range(250000):
        E,ass=rng.choice(configs);a,b,S=profile(E,ass,2)
        if not all(len(S[i])==4 for i in range(4)):continue
        if not all(len(t)>=3 for t in S if t):continue
        if not any(len(t)==3 for t in S):continue
        V,oth=rng.choice(configs[:12]);x,y,T=profile(V,oth,4)
        seen={u^v for l,r in zip(S,T) for u in l for v in r}
        if len(seen)==15:
            print('one-hole',it,E,a,b,V,x,y,sorted(set(range(16))-seen),flush=True)
            print([(m,sorted(t),sorted(T[m])) for m,t in enumerate(S) if t],flush=True);break
    else: print('no examples')
