from itertools import product
from random import Random
from commuting_toggle_rails import compose,count_rails,decode_table,inverse,precedence_blocks


def brute(n,rails):
    results=set()
    for flags in range(1<<n):
        for starts in product(*(range(s) for s,_ in rails)):
            paths=[]
            for start,(_,gates) in zip(starts,rails):
                path=[start]
                for lit,p,q in gates:
                    bit=bool(flags&(1<<(abs(lit)-1))) == (lit>0)
                    path.append((q if bit else p)[path[-1]])
                if path[-1]!=start:
                    break
                paths.append(tuple(path))
            else:
                results.add((flags,tuple(paths)))
    return results


def main():
    rng=Random(3105)
    def perm(size):
        return tuple(rng.sample(range(size),size))
    a,b=(1,0,2),(0,2,1)
    assert precedence_blocks([[(1,a),(2,b)]])==[(1,),(2,)]
    for words in ([[(1,a),(2,b),(1,a)]],[[(1,a),(2,b)],[(2,b),(1,a)]]):
        assert precedence_blocks(words)==[(1,2)]
    ident=tuple(range(6))
    step=tuple((i+1)%6 for i in ident)
    for length in (5,6):
        rails=[(6,[(1,ident,step)]*length)]
        assert count_rails(1,rails)[0]==(6 if length==5 else 12)
    # Construct arbitrary site frames E_i with an unconstrained closing frame;
    # Q_i are rotations, and B a reflection that need not commute with them.
    for trial in range(85):
        n=rng.randrange(1,5)
        rails=[]
        for _ in range(rng.randrange(3)):
            s=rng.randrange(2,6)
            frame=tuple(range(s))
            gates=[]
            for j in range(rng.randrange(1,8)):
                new=perm(s) if j<4 else tuple(reversed(range(s)))
                t=tuple((u+j+1)%s for u in range(s)) if trial%2==0 else perm(s)
                p=compose(new,inverse(frame))
                q=compose(new,compose(t,inverse(frame)))
                assert decode_table(s,[(bit,i,z[i]) for bit,z in enumerate((p,q)) for i in range(s)])==(p,q)
                gates.append((rng.choice((-1,1))*rng.randrange(1,n+1),p,q))
                frame=new
            rails.append((s,gates))
        expected=brute(n,rails)
        count,witness=count_rails(n,rails)
        assert count==len(expected) and (witness in expected if count else witness is None)
    for bad in [[],[(0,0,0),(0,0,1)],[(bit,i,0) for bit,i in product(range(2),repeat=2)]]:
        try:
            decode_table(2,bad)
        except ValueError:
            continue
        raise AssertionError("invalid grouped relation accepted")
    print("85 original-port brute controls, mod-six 5/6 toggles, SCC precedence, corrupt local tables passed")


if __name__=='__main__':
    main()
