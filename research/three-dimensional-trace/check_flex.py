"""Direct finite checks on the exterior tests for weighted rank-two pieces."""
from random import Random


def bit(d,x):
    return (d&x).bit_count()%2


def sums(items):
    out={(0,0)}
    for v,a in items:
        out.update([(w^v,c^a) for w,c in out])
    return out


def test(rank,k,inside,outside,s,t,u):
    boundary_mask=(1<<k)-1
    # Both sides have full boundary span in the ambient representation.
    duals=range(1<<rank)
    table={}
    for d in duals:
        for w,c in sums([(v,l) for v,l in inside if not bit(d,v)]):
            if w<=boundary_mask:
                table.setdefault((w,d&boundary_mask),set()).add(c)
    all_contexts=[]
    for d in duals:
        if not bit(d,s):continue
        for v,c in sums([(a,l) for a,l in outside if not bit(d,a)]):
            w=t^v
            if w<=boundary_mask:
                all_contexts.append((w,d&boundary_mask,c^bit(d,u)))
    actual=set()
    baseline=set()
    for w,dd,c in all_contexts:
        if not bit(dd,w) and (w,dd) in table:
            a=table[w,dd]
            actual.update(c^j for j in a)
            baseline.add(c^min(a))
    has_odd=table.get((0,0))=={0,1}
    if not has_odd:
        assert actual==baseline
        return
    if any(d==0 for _,d,_ in all_contexts):
        assert actual=={0,1}
        return
    flex=False
    for (w,d),values in table.items():
        if len(values)!=2:continue
        if not d:continue
        p=next((j for j in range(1,boundary_mask+1) if not bit(d,j)),0)
        exact=any(v==w and d0==d for v,d0,_ in all_contexts)
        # Exterior trace requires its target t+w to have value zero; every
        # enumerated context has this because it is a sum of selected columns.
        reduced=any(v==w and not bit(d0,p) for v,d0,_ in all_contexts)
        assert exact==reduced
        flex |= reduced
    assert (actual=={0,1}) if flex else (actual==baseline)


if __name__=='__main__':
    rng=Random(817042)
    for trial in range(500):
        k=rng.randrange(3)
        rank=k+3
        inside=[(1<<j,rng.randrange(2)) for j in range(k)]
        outside=[(1<<j,rng.randrange(2)) for j in range(k)]
        for _ in range(4):
            inside.append((rng.randrange(1<<k) | (rng.randrange(2)<<(k+2)),rng.randrange(2)))
            outside.append((rng.randrange(1<<(k+2)),rng.randrange(2)))
        s,t,u=[rng.randrange(1<<(k+2)) for j in range(3)]
        test(rank,k,inside,outside,s,t,u)
    print("500 weighted separator flex decisions verified")
