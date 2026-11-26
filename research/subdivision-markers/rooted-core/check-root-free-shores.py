import random
rng=random.Random(20261126)
def sp(vs):
    out={0}
    for x in vs: out|={a^x for a in out}
    return frozenset(out)
def tab(cols,W):
    t={}
    for s in range(1<<len(cols)):
        F=[v for i,v in enumerate(cols) if (s>>i)&1]
        t[sp(F)&W]=F
    return t
def connected(cols,u,v):
    for s in range(1<<len(cols)):
        E=[x for i,x in enumerate(cols) if (s>>i)&1]+[u,v]
        if len(sp(E))!=1<<(len(E)-1): continue
        if all(len(sp(E[:i]+E[i+1:]))==1<<(len(E)-1) for i in range(len(E))):
            return True
    return False
N=0
for trial in range(320):
    O=[rng.randrange(16) for _ in range(rng.randrange(4,8))]
    ext=[rng.randrange(4)^(rng.randrange(4)<<4) for _ in range(5)]
    W=sp(O)&sp(ext)
    real=tab(O,W)
    S=[h for h in W-{0} if len(W)<4 or connected(O,*list(W-{0,h}))]
    assert set(tab(S,W))==set(real)
    for J,F in real.items():
        for mask in range(4):
            picked=[v for i,v in enumerate(ext[:2]) if mask>>i&1]
            assert sp(picked+F)&sp(ext[2:])==sp(picked+list(J))&sp(ext[2:])
            N+=1
print('320 shores;',N,'exterior substitutions verified')
