"""Small explicit-slot oracle for GF(3) matching assignments."""
from functools import cache
from itertools import combinations, permutations, product
from random import Random


def add(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))


def sub(a,b):
    return tuple((x-y)%3 for x,y in zip(a,b))


def total(vectors,zero):
    value=zero
    for v in vectors:
        value=add(value,v)
    return value


def brick():
    # One pendant triangle for each of the three principal pools, m=1.
    ds=((0,1),(1,0),(1,1))
    edges={}
    for u,v in combinations(range(18),2):
        if v<9:
            edges[u,v]=ds[u//3] if u//3==v//3 else (0,0)
        elif u<9 and u//3==(v-9)//3:
            edges[u,v]=add(ds[u//3],ds[u//3])
        elif u>=9 and (u-9)//3==(v-9)//3:
            edges[u,v]=(0,0)
    @cache
    def table(mask):
        if not mask:
            return {(0,0):()}
        u=(mask&-mask).bit_length()-1
        result={}
        for v in range(u+1,18):
            if mask>>v&1 and (u,v) in edges:
                for h,tr in table(mask^(1<<u)^(1<<v)).items():
                    result.setdefault(add(edges[u,v],h),((u,v),)+tr)
        return result
    shift=(1,1)
    ans={sub(h,shift):tr for h,tr in table((1<<18)-1).items()}
    assert set(ans)=={(0,0),(0,1),(1,0),(1,1),(2,2)}
    for h,tr in ans.items():
        assert sorted(v for pair in tr for v in pair)==list(range(18))
        assert sub(total((edges[p] for p in tr),(0,0)),shift)==h
    return tuple(ans)


def extend(space,v):
    return frozenset(space|{add(h,v) for h in space}|{sub(h,v) for h in space})


def directions(slot,z):
    baseline=slot[0]
    space=frozenset((z,))
    actual=[]
    for other in slot[1:]:
        v=sub(other,baseline)
        if v not in space:
            space=extend(space,v)
            actual.append((v,other))
    return space,actual


def certify(slots,b):
    z=(0,)*b
    s=(4*b-1).bit_length()
    domain=tuple(product(range(3),repeat=b))
    full=frozenset(domain)
    spaces={frozenset((z,)):0}
    for v in domain:
        for U,dim in tuple(spaces.items()):
            if v not in U:
                spaces[extend(U,v)]=dim+1
    dirs=[directions(slot,z) for slot in slots]
    for U,u in sorted(spaces.items(),key=lambda p:-p[1]):
        exc=tuple(i for i,(span,_) in enumerate(dirs) if not span<=U)
        if len(exc)>s*(b-u):
            continue
        eligible=[i for i in range(len(slots)) if i not in exc]
        def pack(left,group,span,remaining,used):
            if len(group)==u:
                if remaining==1:
                    return used+group
                return pack(left,(),frozenset((z,)),remaining-1,used+group)
            for i in left:
                if group and i<=group[-1][0]:
                    continue
                for v,other in dirs[i][1]:
                    if v not in span:
                        found=pack(tuple(j for j in left if j!=i),group+((i,v,other),),
                                   extend(span,v),remaining,used)
                        if found is not None:
                            return found
            return None
        if len(eligible)<s*u:
            continue
        tokens=pack(tuple(eligible),(),frozenset((z,)),s,())
        if tokens is None:
            continue
        assert len({i for i,v,other in tokens})==s*u
        for block in range(s):
            span=frozenset((z,))
            for i,v,other in tokens[block*u:(block+1)*u]:
                assert other in slots[i] and sub(other,slots[i][0])==v and v not in span
                span=extend(span,v)
            assert span==U
        toggles={z:()}
        for i,v,other in tokens:
            for g,w in tuple(toggles.items()):
                toggles.setdefault(add(g,v),w+((i,other),))
        assert set(toggles)==U
        # Only exceptional profiles are needed in the quotient.
        base=[slot[0] for slot in slots]
        quotient={}
        for values in product(*(slots[i] for i in exc)):
            chosen=base.copy()
            for i,val in zip(exc,values):
                chosen[i]=val
            g=total(chosen,z)
            representative=min(add(g,h) for h in U)
            quotient.setdefault(representative,(g,chosen))
        found={}
        for g,chosen in quotient.values():
            for h,trace in toggles.items():
                witness=chosen.copy()
                for i,choice in trace:
                    witness[i]=choice
                t=add(g,h)
                assert total(witness,z)==t and all(val in slot for val,slot in zip(witness,slots))
                found[t]=tuple(witness)
        if sum(len(slot)>1 for slot in slots)>s*b:
            assert u>0
        return found,u
    raise AssertionError('no rank-descent certificate')


def audit(matrix,mandatory,b):
    z=(0,)*b
    n=len(matrix)
    expected=set()
    restored={}
    dimensions=[]
    for perm in permutations(range(n)):
        slots=tuple(mandatory)+tuple(matrix[i][j] for i,j in enumerate(perm))
        if any(not slot for slot in slots):
            continue
        reachable={z}
        for slot in slots:
            reachable={add(h,x) for h in reachable for x in slot}
        predicted,u=certify(slots,b)
        assert set(predicted)==reachable
        dimensions.append(u)
        expected|=reachable
        for t,w in predicted.items():
            restored[t]=(perm,w)
    assert set(restored)==expected
    return dimensions


if __name__=='__main__':
    rng=Random(766)
    domain=tuple(product(range(3),repeat=2))
    assignments=0
    for j in range(120):
        def slot(k):
            return tuple(rng.sample(domain,k))
        rows=[[slot(rng.randrange(4)) for c in range(3)] for r in range(3)]
        extras=[slot(rng.randrange(1,4)) for k in range(rng.randrange(4))]
        assignments+=len(audit(rows,extras,2))
    e0=((0,0),(1,0))
    e1=((0,0),(0,1))
    assert audit([], [e0,e1]*3,2)==[2]
    assert audit([], [e0]*7+[e1],2)==[1]
    assert audit([], [brick()],2)==[0]
    for k in range(8):
        assert audit([], [((0,),(1,))]*k,1)==[int(k>=2)]
    print('120 sparse rank-two matrices,',assignments,'feasible assignments, full/partial/zero rank, scalar k=0..7 and original-edge brick passed')
