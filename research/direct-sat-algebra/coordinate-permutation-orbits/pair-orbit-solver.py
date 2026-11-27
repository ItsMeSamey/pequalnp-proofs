"""Polynomial zero-subcube solver on the recognizable swap-matching class.
Returns ('outside',None), ('no',None) or ('yes',list of conjugate indices).
"""
from orbit_subcube import move

def solve(R,F,start,pins):
    d=len(R)
    if sorted(R)!=list(range(d)) or sorted(F)!=list(range(d)) or min(start,pins)<0 or (start|pins)>>d:
        raise ValueError("invalid instance")
    if move(R,start)!=start or any(F[F[i]]!=i for i in range(d)):
        return 'outside',None
    swaps={(i,F[i]) for i in range(d) if i<F[i]}
    allpairs=set(swaps);todo=list(swaps)
    for i,j in todo:
        nxt=tuple(sorted((R[i],R[j])))
        if nxt not in allpairs:allpairs.add(nxt);todo.append(nxt)
    if len({p for pair in allpairs for p in pair})!=2*len(allpairs):return 'outside',None
    pairs=sorted(allpairs);index={p:i for i,p in enumerate(pairs)}
    orbit=[index[tuple(sorted((R[i],R[j])))] for i,j in pairs]
    vector=sum(1<<index[z] for z in swaps)
    # Delta to pinned output bits caused by each disjoint transposition.
    response=[(((1<<i)|(1<<j))&pins) if ((start>>i)^(start>>j))&1 else 0 for i,j in pairs]
    span={};images={};j=0
    while True:
        z=vector
        while z and z.bit_length() in span:z^=span[z.bit_length()]
        if not z:break
        span[z.bit_length()]=z
        s=0;cert=1<<j
        for i,value in enumerate(response):
            if vector>>i&1:s^=value
        while s and s.bit_length() in images:
            a,c=images[s.bit_length()];s^=a;cert^=c
        if s:images[s.bit_length()]=s,cert
        vector=move(orbit,vector);j+=1
    goal=start&pins;cert=0
    while goal:
        if goal.bit_length() not in images:return 'no',None
        a,c=images[goal.bit_length()];goal^=a;cert^=c
    powers=[i for i in range(j) if cert>>i&1]
    return 'yes',powers

if __name__=='__main__':
    from random import Random
    rng=Random(27);cases=0
    for m in range(1,8):
        for _ in range(15):
            shuffle=list(range(m));rng.shuffle(shuffle)
            r=[2*shuffle[i//2]+(i%2) for i in range(2*m)]
            f=[i^((v>> (i//2))&1) for v in [rng.randrange(1<<m)] for i in range(2*m)]
            start=sum(1<<(2*i) for i in range(m));pins=rng.randrange(1<<(2*m))
            seen={start};queue=[start]
            for s in queue:
                for p in (r,f):
                    w=move(p,s)
                    if w not in seen:seen.add(w);queue.append(w)
            good=any(not s&pins for s in seen);status,powers=solve(r,f,start,pins)
            assert (status=='yes')==good
            if good:
                inv=[r.index(i) for i in range(2*m)];s=start
                for j in powers:
                    for i in range(j):s=move(inv,s)
                    s=move(f,s)
                    for i in range(j):s=move(r,s)
                assert s in seen and not s&pins
            cases+=1
    print(cases,'comparison and actual conjugate witnesses')
