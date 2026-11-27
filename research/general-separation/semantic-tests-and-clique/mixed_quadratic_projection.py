"""Degree profiles and the open two-site table for an eight-vertex mixed graph."""
from itertools import combinations

ROWS=(38,97,129,208,40,147,138,108)
C=21


def bits(x):
    while x:
        low=x&-x
        yield low.bit_length()-1
        x^=low


def profile(d,pins):
    n=len(ROWS)
    mons=[sum(1<<i for i in s) for j in range(d+1) for s in combinations(range(n),j)]
    idx={m:i for i,m in enumerate(mons)}
    B={};pending=[]
    def reduce(z):
        while z and z.bit_length() in B:
            z^=B[z.bit_length()]
        return z
    def insert(z):
        z=reduce(z)
        if z:
            B[z.bit_length()]=z
            if mons[z.bit_length()-1].bit_count()<d:
                pending.append(z)
    for i,row in enumerate(ROWS):
        g=(1<<idx[1<<i]) if C>>i&1 else 0
        for j in bits(row):
            g^=1<<idx[(1<<i)|(1<<j)]
        insert(g)
    for i in pins:
        insert(1 | (1<<idx[1<<i]))
    for g in pending:
        for i in range(n):
            w=0
            for j in bits(g):
                w^=1<<idx[mons[j]|(1<<i)]
            insert(w)
    pair=1<<idx[129]
    return len(B),sum(mons[k-1].bit_count()<=2 for k in B),not reduce(pair),not reduce(1)


def check():
    states=set()
    raw_pairs=set()
    legal=[]
    for w in range(256):
        z=C^sum((((r&w).bit_count()%2)<<i) for i,r in enumerate(ROWS))
        if not (z&w):
            legal.append(w)
        if w&z&126:
            continue
        raw_pairs.add(((w&1)|((w>>6)&2),(z&1)|((z>>6)&2)))
        for t in range(4):
            drift=(t&1)|((t>>1)<<7)
            if not w&(z^drift):
                states.add(((w&1)|((w>>6)&2),t))
    assert len(legal)==23 and all((w&129)!=129 for w in legal)
    assert states=={(s,t) for s in range(4) for t in range(4)}-{(3,0)}
    assert raw_pairs==states
    from bounded_cubic_pin_pc import pc, flat_truth
    physical=[294,97,1153,208,1064,147,138,1644,513,384,148]
    pins=(8,9,10)
    assert not flat_truth(physical,pins)
    assert pc(physical,pins,2)[0] and pc(physical,pins,3)[0]
    profiles=[(d,profile(d,()),profile(d,(0,7))) for d in (2,3,4)]
    assert [u[2] for _,u,_ in profiles]==[False,False,True]
    assert all(v[3] for _,_,v in profiles)
    print(len(legal),"legal words;",len(states),"open states;",profiles)


if __name__=="__main__":
    check()
