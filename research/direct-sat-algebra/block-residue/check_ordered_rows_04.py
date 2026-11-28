"""Independent finite order search and original NAND replay."""
from itertools import combinations, product
from ordered_row_csp import ordered_assignment, solve


def exists(ds,rs,m):
    for bits in product(range(2),repeat=len(ds)):
        orders = [sorted(d) for d in ds]
        for s,b in zip(orders,bits):
            if m=='min' and b:
                s.reverse()
            if m=='median' and b and len(s)>=3:
                s[0],s[1]=s[1],s[0]
        k = 2 if m=='min' else 3
        if all(tuple(sorted(col,key=seq.index)[k-2] for col,seq in
                     zip(zip(*chosen),(orders[i],orders[j]))) in r
               for (i,j),r in rs.items() for chosen in combinations(r,k)):
            return True
    return False


def chart(ds,rs):
    adj=[{} for d in ds]
    for (i,j),r in rs.items():
        adj[i][j]=r
        adj[j][i]={(b,a) for a,b in r}
    sols={s for s in product(*ds) if all((s[i],s[j]) in r for (i,j),r in rs.items())}
    for mode in ('min','median','auto'):
        modes = ('min','median') if mode=='auto' else (mode,)
        method=next((m for m in modes if exists(ds,rs,m)),None)
        status,used,result=ordered_assignment(ds,adj,mode=mode)
        assert used==method
        assert status==('skip' if not method else ('sat' if sols else 'unsat'))
        if status=='sat':
            assert tuple(result[i] for i in range(len(ds))) in sols
        else:
            assert result is None
    return sols


def replay(raw,gates):
    w=list(raw)
    for a,b in gates:
        w.append(int(not(w[a] and w[b])))
    return w


def physical(perms,expected,strict_cycle=False):
    n=7
    gates,misses=[],[]
    def add(a,b):
        gates.append((a,b))
        return n+len(gates)-1
    for x,p in ((0,1),(2,3),(4,5)):
        o=add(x,p)
        e=add(o,p)
        t=add(e,add(p,p))
        misses.append([t,e,o])
    rs={}
    clauses=[(7,)]
    for ports in misses:
        clauses.extend((7,w+1) for w in ports)
    for i,j in combinations(range(3),2):
        allowed=set(zip(perms[i],perms[j]))
        if strict_cycle:
            allowed={(a,b) for a,b in product(range(3),repeat=2)
                     if (a<b if (i,j)!=(0,2) else a>b)}
        rs[i,j]=allowed
        clauses.extend((misses[i][a]+1,misses[j][b]+1)
                       for a,b in product(range(3),repeat=2) if (a,b) not in allowed)
    assert len(chart([list(range(3))]*3,rs))==(0 if strict_cycle else 3)
    def ok(raw):
        w=replay(raw,gates)
        return all(any(w[l-1] for l in row) for row in clauses)
    assert any(ok(raw) for raw in product(range(2),repeat=n)) == (not strict_cycle)
    state,stats,raw=solve(n,gates,clauses=clauses)
    assert stats['bad']==3 and stats['method']==expected
    assert state==('unsat' if strict_cycle else ('sat' if expected else 'skip'))
    assert ok(raw) if state=='sat' else raw is None


def main():
    d=[0,1,2]
    physical([d,[1,0,2],d],'median')
    physical([d,d,d],'min',strict_cycle=True)
    physical([d,d,d],'min')
    physical([d,[1,2,0],[2,0,1]],None)
    d=[2,5,9,13]
    perms=[d,[5,2,9,13],d]
    chart([d]*3,{(i,j):set(zip(perms[i],perms[j])) for i,j in combinations(range(3),2)})
    chart([d]*3,{(i,j):{(a,b) for a,b in product(d,repeat=2)
                       if (a<b if (i,j)!=(0,2) else a>b)} for i,j in combinations(range(3),2)})
    print('cyclic candidate search, median-only SAT, missed chart')


if __name__=='__main__':
    main()
