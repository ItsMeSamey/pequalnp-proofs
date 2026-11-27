"""Deterministic two-quotient recognizer; U occupies the low 4 bits and H=<e0,e1>."""
from collections import deque
from itertools import combinations,combinations_with_replacement
from quadratic_centroid import independent
from quadratic_target import reduce_vector


def wedge(a,b):
    return sum(((((a>>i)&1)*((b>>j)&1))^(((a>>j)&1)*((b>>i)&1)))<<k
               for k,(i,j) in enumerate(combinations(range(4),2)))


def common_basis(left,right,k):
    I=set()
    def ok(A,S):
        return len(independent(A[i] for i in S))==len(S)
    while len(I)<k:
        outside=set(range(len(left)))-I
        parent={e:None for e in sorted(outside) if ok(left,I|{e})}
        queue=deque(parent)
        sink=None
        while queue:
            u=queue.popleft()
            if u in I:
                adj=[v for v in sorted(outside) if v not in parent and ok(left,(I-{u})|{v})]
            else:
                if ok(right,I|{u}):
                    sink=u
                    break
                adj=[v for v in sorted(I) if v not in parent and ok(right,(I-{v})|{u})]
            for v in adj:
                parent[v]=u
                queue.append(v)
        if sink is None:
            return None
        while sink is not None:
            I.symmetric_difference_update((sink,))
            sink=parent[sink]
    return tuple(sorted(I))


def trace(columns,indices):
    pivots={}
    deps=[]
    for i in indices:
        rem,label=reduce_vector(columns[i]>>4,pivots)
        name=(columns[i]&15)^label
        if rem:
            pivots[rem.bit_length()-1]=(rem,name)
        else:
            deps.append(name)
    return wedge(*deps) if len(deps)==2 else 0


planes={wedge(a,b):(a,b) for a,b in combinations(range(1,16),2)}
forms=sorted(v for v in planes if v&1)
decoys=sorted(set(planes)-{1})
pairs=tuple(combinations_with_replacement(forms,2))


def accepts(pair,p):
    return all((w&p).bit_count()%2 for w in pair)


def solve(columns):
    columns=tuple(columns)
    if any(type(x) is not int or x<0 for x in columns):
        raise ValueError("invalid packed column")
    rank=len(independent(x>>4 for x in columns))+2
    def projection(w):
        a,b=planes[w]
        return [((x>>4)<<2)|((a&x).bit_count()%2)|(((b&x).bit_count()%2)<<1)
                for x in columns]
    seen={}
    while True:
        pair=next((q for q in pairs if all(not accepts(q,p) for p in seen)),None)
        if pair is None:
            return "UNKNOWN",None,seen
        basis=common_basis(projection(pair[0]),projection(pair[1]),rank)
        if basis is None:
            return "NO",None,seen
        p=trace(columns,basis)
        assert accepts(pair,p)
        if p==1:
            return "YES",basis,seen
        seen[p]=basis


def self_test():
    from random import Random
    masks=sorted({sum(1<<i for i,p in enumerate(decoys) if accepts(q,p)) for q in pairs},
                 key=int.bit_count)
    def hits(todo,k):
        if not todo:
            return True
        if not k:
            return False
        choices=todo[0]
        while choices:
            bit=choices&-choices
            choices^=bit
            if hits([e for e in todo if not (e&bit)],k-1):
                return True
        return False
    assert not hits(masks,5)
    assert all(any(accepts(q,p) for p in (2,3,4,5,6,7)) for q in pairs)
    # All six Fano decoys can also occur as the entire physical NO instance.
    coset=(4,5,6,7)
    status,_,seen=solve(coset)
    assert status=="UNKNOWN" and len(seen)==6
    def lift(p):
        return sum((((p>>i)&(p>>j))&1)<<k for k,(i,j) in enumerate(
            combinations_with_replacement(range(6),2)))
    def liftspan(cols):
        b=independent(lift(trace(cols,I)) for I in combinations(range(len(cols)),2))
        return {sum_xor(b,mask) for mask in range(1<<len(b))}
    def sum_xor(b,mask):
        x=0
        for i,v in enumerate(b):
            if mask>>i&1: x^=v
        return x
    assert liftspan(coset)==liftspan((*coset,1,2))
    rng=Random(591)
    for _ in range(150):
        r=rng.randrange(4)
        columns=[rng.randrange(1<<(r+4)) for j in range(rng.randrange(2,10))]
        k=len(independent(x>>4 for x in columns))+2
        actual={trace(columns,I) for I in combinations(range(len(columns)),k)}
        actual.discard(0)
        status,basis,seen=solve(columns)
        assert status!="NO" or 1 not in actual
        assert status!="YES" or trace(columns,basis)==1
        assert status!="UNKNOWN" or len(seen)>=6
        assert all(trace(columns,s)==p for p,s in seen.items())
        assert len(actual-{1})>5 or status==("YES" if 1 in actual else "NO")
    print("136 pairs, sharp six-decoy covering obstruction, 150 exhaustive private-rank cases passed")


if __name__=="__main__":
    self_test()
