"""Original physical box fibers and an attained twelve-state strict tail guard."""
from itertools import combinations


def table(rows,c):
    n=len(rows)
    reps={}
    for w in range(1<<n):
        defect=c ^ sum(((r&w).bit_count()%2)<<i for i,r in enumerate(rows))
        if not w&defect&~3:
            reps.setdefault((w&3,defect&3),w)
    return reps


def strict(reps,force_b,shift_a):
    # At a=1 let force_b[b] be required f if b selected and shift_a[b] the
    # external contribution to e. Any affine drift on the two occupancies
    # restricts to some such pair of values on this two-point slice.
    return {((d&1)^shift_a[s>>1]) for s,d in reps if s&1 and
            (s==1 or (d>>1)==force_b)}


def check():
    rows=[4,24,1,2,2]
    c=16
    reps=table(rows,c)
    assert len(reps)==12 and strict(reps,0,[0,0])=={0}
    print("rows",rows,"c",c,"(occupancy, defect):full mask",sorted(reps.items()))
    assert {s:sorted(d for a,d in reps if a==s) for s in range(4)}=={
        0:[0,1,2,3],1:[0,2],2:[0,1,2,3],3:[0,2]}
    total=0
    for n in range(2,6):
        pairs=list(combinations(range(n),2))
        for g in range(1<<len(pairs)):
            A=[0]*n
            for j,(u,v) in enumerate(pairs):
                if g>>j&1:
                    A[u]|=1<<v
                    A[v]|=1<<u
            for drift in range(0,1<<n,4):
                got=table(A,drift)
                if len({d&1 for s,d in got if s==1})==1:
                    assert sum(s==3 for s,d in got) in (1,2,4)
                if len(got)>=13:
                    for b,x in ((a,x) for a in (0,1) for x in (0,1)):
                        assert len(strict(got,b,[0,x]))==2
                total+=1
    print("small raw graph/private-drift systems",total)


if __name__=="__main__":
    check()
