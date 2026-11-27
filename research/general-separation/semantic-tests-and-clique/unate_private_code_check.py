"""Exhaustive canonical codes for patterns of consistently signed conjunctions."""
from itertools import combinations
from random import Random


def bits(mask):
    return [i for i in range(mask.bit_length()) if mask>>i&1]


def unite(items):
    out=0
    for item in items:out|=item
    return out


def pattern(x,edges):
    return sum(int(x&e==e)<<i for i,e in enumerate(edges))


def check_packing(n,edges,unions):
    blocks=[]
    used=0
    for j in range(n):
        center=1<<j
        if center in edges:continue
        successors=[]
        for e in edges:
            if e&center:
                order=bits(e)
                successors.append(1<<order[(order.index(j)+1)%len(order)])
        neighbors=unite(successors)
        b=center|neighbors
        if b&used:continue
        blocks.append((b,center))
        used|=b
    blocks.extend((1<<i,None) for i in range(n) if not used>>i&1)
    # Mixed-radix enumerator visits each legal packed word once. The full
    # canonical mask can still reject words after local forbidden patterns.
    alphabets=[[unite(1<<j for k,j in enumerate(bits(b)) if a>>k&1)
                for a in range(1<<b.bit_count())] for b,_ in blocks]
    for alphabet,(_,bad) in zip(alphabets,blocks):
        if bad is not None:alphabet.remove(bad)
    capacity=1
    for alphabet in alphabets:capacity*=len(alphabet)
    accepted=set()
    candidates=set()
    for code in range(1<<(capacity-1).bit_length()):
        if code>=capacity:continue
        word=0
        for alphabet in alphabets:
            code,digit=divmod(code,len(alphabet))
            word|=alphabet[digit]
        assert code==0 and word not in candidates
        candidates.add(word)
        if unite(e for e in edges if e&word==e)==word:accepted.add(word)
    assert accepted==unions and len(candidates)==capacity


def check(n,edges,flips):
    images={}
    for raw in range(1<<n):
        x=raw^flips
        y=pattern(x,edges)
        images.setdefault(y,[]).append(x)
    unions={unite(edges[i] for i in bits(mask)) for mask in range(1<<len(edges))}
    for y,fiber in images.items():
        rep=unite(edges[i] for i in bits(y))
        assert pattern(rep,edges)==y and rep in fiber
        assert all(rep&x==rep for x in fiber)
        assert rep==min(fiber,key=int.bit_count)
    assert len(images)==len(unions)
    for x in range(1<<n):
        valid=x in unions
        assert valid==(unite(e for e in edges if e&x==e)==x)
    # Cartesian blocks: enumerate each local union exactly once, combine by OR.
    components=[]
    for e in edges:
        if not e:continue
        touched=[c for c in components if c&e]
        components=[c for c in components if c not in touched]
        components.append(e|unite(touched))
    combined={0}
    for comp in components:
        local=[e for e in edges if e and e&comp]
        words={unite(local[i] for i in bits(s)) for s in range(1<<len(local))}
        combined={a|b for a in combined for b in words}
    assert combined==unions
    check_packing(n,edges,unions)
    return len(images)


def main():
    rng=Random(388)
    for n in range(2,6):
        star=[1|(1<<i) for i in range(1,n)]
        clique=[(1<<a)|(1<<b) for a,b in combinations(range(n),2)]
        assert check(n,star,rng.randrange(1<<n))==1<<(n-1)
        assert check(n,clique,rng.randrange(1<<n))==(1<<n)-n
    assert check(7,[3,5,6,24,40,48],87)==25
    for n,edges in [(5,[3,6,12,24,17]),(7,[1,2,2,7,28,112,0]),(6,[]),(4,[0,0])]:
        check(n,edges,rng.randrange(1<<n))
    for _ in range(80):
        n=rng.randrange(1,8)
        check(n,[rng.randrange(1<<n) for _ in range(rng.randrange(10))],rng.randrange(1<<n))


if __name__=='__main__':
    main()
    print('canonical fibers, signed inputs, block products, star and clique counts passed')
