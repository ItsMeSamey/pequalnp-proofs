"""Fresh bounded original physical oracle for scheduler 04; run as a script."""
from itertools import product
from random import Random
from shell_stream import Shell


def audit(n,edges,blocks,weights,lists,cols,target,obs,p):
    obj=Shell(n,edges,blocks,weights,lists,cols,target,obs,p)
    expected={}
    for colors in product(range(4),repeat=n):
        if not all(lists[i]&(1<<v) for i,v in enumerate(colors)):continue
        pairs=list(edges)
        for A,B,m in blocks:pairs.extend((a,b,m) for a in A for b in B)
        if any(not (m&(1<<(colors[a]^colors[b]))) for a,b,m in pairs):continue
        bits=tuple((v>>b)&1 for v in colors for b in (0,1))
        syndrome=0
        weight=1
        for i,v in enumerate(bits):
            if v:syndrome^=cols[i]
        if syndrome!=target:continue
        for i,v in enumerate(colors):weight*=weights[i][v]
        word=tuple(v for v,keep in zip(bits,obs) if keep)
        expected.setdefault(word,[]).append((colors,weight))
    mod=1<<p
    live=set()
    for word in product((0,1),repeat=sum(obs)):
        rows=expected.get(word,[])
        residue,witness=obj.fiber(word)
        assert residue==sum(w for _,w in rows)%mod
        assert (witness in {c for c,_ in rows}) if rows else witness is None
        if residue:live.add(word)
    answer=obj.nonzero_fiber()
    assert (answer is not None)==bool(live)
    if answer:
        word,residue,witness=answer
        assert word in live and (residue,witness)==obj.fiber(word)


def main():
    rng=Random(4007)
    for trial in range(12):
        n=4
        blocks=[((0,2),(1,3),rng.choice((7,11,13,14,15))),
                ((0,1),(3,),rng.choice((7,14,15)))]
        edges=[(1,2,rng.choice((5,10,14,15))),(3,3,15)]
        weights=[tuple(rng.randrange(-2,4) for _ in range(4)) for i in range(n)]
        obs=[(i+trial)%2 for i in range(2*n)]
        audit(n,edges,blocks,weights,[15]*n,[rng.randrange(4) for _ in obs],
              rng.randrange(4),obs,1+trial%3)
    for p in (1,2,3):
        audit(2,[],[((0,),(1,),14)],[(1,)*4]*2,[15]*2,[0]*4,0,[0]*4,p)
    for target in (0,1):audit(0,[],[],[],[],[],target,[],2)
    audit(1,[(0,0,14)],[],[(1,)*4],[15],[0,0],0,[1,1],2)
    print("18 shell fixtures: brute physical fibers, signed residues, replay, module identity")

if __name__=="__main__":main()
