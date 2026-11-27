"""Independent bag/edge replay, including inverse caps on exceptional rooted forms."""
from collections import Counter
from degree_five_periodic_prime import chain
from high_pin_odd_pair import find
from odd_support_path_decomposition import construct
import exceptional_terminal_replay as terminals


def lists(rows):
    return [[v for v in range(len(rows)) if r >> v & 1] for r in rows]


def check(rows,p,q):
    graph=lists(rows)
    ans=construct(graph,[p,q])
    assert ans['status']=='CERTIFIED'
    bags=[set(b) for b in ans['bags']]
    assert ans['width']==max(map(len,bags))-1 <= 7
    for v,row in enumerate(graph):
        idx=[i for i,b in enumerate(bags) if v in b]
        assert idx and idx==list(range(idx[0],idx[-1]+1))
        assert all(any({v,w}<=b for b in bags) for w in row)
    return len(bags)


def parents(rows):
    common=[i for i in range(len(rows)) if rows[0]>>i&1]
    n=len(rows)
    for adjacent in (False,True):
        rr=list(rows)+[0,0]
        edges=[(1,j) for j in common]+[(n,j) for j in common]+[(n,n+1)]
        edges+= [(1,0),(n,0)] if adjacent else [(n,1)]
        for a,b in edges:
            rr[a]^=1<<b
            rr[b]^=1<<a
        yield rr,n+1,0


def main():
    for n in (0,1,2,5,32,128):
        r,p,q=chain(n)
        check(r,p,q)
    for r,p,q in (([224,112,104,84,42,87,47,1],3,5),([52,56,41,38,35,31],0,1)):
        assert find(lists(r),[p,q])['high_pin_minimal']
        check(r,p,q)
    roots=list(terminals.starts())
    native=terminals.witnesses
    tested=Counter()
    def replay(rows,p,q):
        assert native(rows,p,q)
        for rr,a,b in parents(rows):
            assert native(rr,a,b)
            assert check(rr,a,b)==4
            tested[sum(r.bit_count()==1 for r in rows)]+=1
        return True
    terminals.witnesses=replay
    try:
        for budget in (0,1):
            terminals.run(roots,budget)
    finally:
        terminals.witnesses=native
    print('inverse caps from orbit representatives',dict(tested),'chain orders through 516')


if __name__=='__main__':
    main()
