from itertools import product
from random import Random
from ternary_global_rows import gadget,partition,solve


def decode_all(built,n):
    if built is None:
        return set()
    size,edges,target,base,tags=built
    incident=[[] for _ in range(size)]
    for j,(a,b,lab) in enumerate(edges):
        incident[a].append((j,b,lab))
        incident[b].append((j,a,lab))
    seen=set()
    def visit(left,goal,flips):
        if not left:
            if not any(goal):
                seen.add(tuple((-base[i] if i in flips else base[i])%3 for i in range(n)))
            return
        a=min(left)
        for j,b,lab in incident[a]:
            if b in left:
                visit(left-{a,b},tuple((x-y)%3 for x,y in zip(goal,lab)),
                      flips|({tags[j]} if j in tags else set()))
    visit(set(range(size)),target,set())
    return seen


def main():
    rng=Random(192)
    checked=0
    for k in range(36):
        n=5
        rows=[tuple([rng.choice((1,2)) for i in range(4)]+[0])]
        if k%3:
            rows.append(tuple([0]+[rng.choice((1,2)) for i in range(4)]))
        rows.append(tuple(rng.randrange(3) for i in range(n)))
        g=[len(rows)-1]
        fixed={0:rng.choice((1,2))} if k%2 else {}
        expected={s for s in product((1,2),repeat=n) if all(s[i]==v for i,v in fixed.items())
                  and all(sum(a*b for a,b in zip(row,s))%3==0 for row in rows)}
        assert decode_all(gadget(n,rows,g,fixed),n)==expected
        checked+=1
    rows=[(1,1,1,1)]*3
    assert partition(rows,0,3) is None and partition(rows,0,4) is not None
    assert partition(rows,1,0) is not None
    for rows in [[(1,1,1,1)],[(1,1,1,1),(1,0,0,1)],[(1,0,0,0)]]:
        s,w=solve(4,rows,b=1,h=1,rounds=3,randbelow_fn=rng.randrange)
        expected=any(all(sum(a*b for a,b in zip(row,x))%3==0 for row in rows)
                     for x in product((1,2),repeat=4))
        assert (s=="SAT")==expected
    print(checked,"exact matching/sign set comparisons; 3 native oracle calls passed")


if __name__=="__main__":
    main()
