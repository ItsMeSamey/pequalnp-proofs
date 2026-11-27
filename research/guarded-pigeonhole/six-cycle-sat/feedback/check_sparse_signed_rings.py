"""Direct permutation audit of two-ring signed bundles and native erasures."""
from itertools import product
from check_ordered_probe_and import cycle

F=(0,2,3,1)
Q=((1,2,0,3),(2,1,3,0))

def local(mode):
    p=F
    for i,q in enumerate(Q):
        if mode>>i&1:
            p=tuple(p[x] for x in q)
    return p

def orbit(p,a):
    out=[a];x=p[a]
    while x!=a:
        out.append(x);x=p[x]
    return out

def build(blocks,modes,good_order,bad_order,slots):
    nv=len(modes);n=len(blocks);base=4*nv
    labels=[base+3*i for i in range(n)]
    p=list(range(base+3*n+1));pool=len(p)-1
    for i,mode in enumerate(modes):
        for j,k in enumerate(local(mode)):
            p[4*i+j]=4*i+k
    # Insert fixed u,v paths immediately before their variable's P,N seam.
    for i in range(nv):
        for sign in (0,1):
            dst=4*i+2+sign;src=p.index(dst)
            for j in range(n):
                if blocks[j]==(i,sign):
                    u=labels[j];p[src]=u;p[u]=u+1;src=u+1
            p[src]=dst
    cycle(p,[pool]+[labels[j]+2 for j in slots])
    stitch=list(range(len(p)))
    cycle(stitch,[4*i for i in good_order])
    cycle(stitch,[4*i+1 for i in bad_order]+[pool])
    return [stitch[x] for x in p],labels

def check(blocks,good_order,bad_order,slots):
    nv=len(good_order);n=len(blocks);tested=0
    attained=set()
    for modes in product(range(4),repeat=nv):
        p,us=build(blocks,modes,good_order,bad_order,slots)
        for erase in range(1<<n):
            q=list(range(len(p)))
            for j,u in enumerate(us):
                if erase>>j&1:cycle(q,[u,u+1,u+2])
            closed=[p[x] for x in q]
            G=orbit(closed,0);B=orbit(closed,1)
            assert set(G).isdisjoint(B) and len(G)+len(B)==len(closed)
            good={j for j,u in enumerate(us) if u+1 in G}
            assert good=={j for j,(i,s) in enumerate(blocks)
                          if modes[i]==s+1 and not erase>>j&1}
            for j,u in enumerate(us):
                if erase>>j&1:assert closed[u+2]==u+1
            attained.add(frozenset(good));tested+=1
    expected={frozenset(j for j in range(n) if x>>j&1) for x in range(1<<n)
              if all(len({s for j,(i,s) in enumerate(blocks) if i==k and x>>j&1})<=1
                     for k in range(nv))}
    assert expected==attained
    return tested,len(expected)

if __name__=='__main__':
    assert [orbit(local(m),1) for m in range(4)]==[[1,2,3],[1,3],[1,2],[1,3,2]]
    cases=[
        ([(0,0),(1,1),(0,1),(1,0)], [0,1],[1,0],[0,2,3,1]),
        ([(0,1),(1,0),(2,1),(0,1),(0,0)], [2,0,1],[1,0,2],[4,2,0,3,1]),
    ]
    print([check(*c) for c in cases])
