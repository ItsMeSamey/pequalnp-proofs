"""GF(4), w^2=w+1. Factor tables use least-significant scope coordinate first."""
from itertools import product
from functools import reduce


def mul(x,y):
    return (x if y&1 else 0) ^ ((x<<1 ^ (7 if x&2 else 0)) if y&2 else 0)


def times(values):
    return reduce(mul,values,1)


def partition(factors):
    factors=list(factors)
    while pool:={v for scope,_ in factors for v in scope}:
        def neighbors(v):
            return set().union(*(set(scope) for scope,_ in factors if v in scope))
        v=min(pool,key=lambda i:(len(neighbors(i)),i))
        used=[f for f in factors if v in f[0]]
        factors=[f for f in factors if v not in f[0]]
        rest=tuple(sorted({u for scope,_ in used for u in scope if u != v}))
        assert len(rest)<=10
        tab=[]
        for word in range(1<<len(rest)):
            env={a:word>>j&1 for j,a in enumerate(rest)}
            values=[]
            for x in (0,1):
                env[v]=x
                values.append(times(t[sum(env[a]<<j for j,a in enumerate(scope))]
                                    for scope,t in used))
            tab.append(values[0]^values[1])
        factors.append((rest,tab))
    return times(tab[0] for _,tab in factors)


def matmul(a,b):
    return [[mul(a[i][0],b[0][j])^mul(a[i][1],b[1][j]) for j in range(2)]
            for i in range(2)]


def physical(edges,activities,t):
    q=mul(t,mul(1^t,1^t))
    k=1^mul(t,t)
    clauses=[[] for _ in activities]
    raw=[]
    def coordinate(y):
        raw.append(((len(raw),),(y,1^y)))
        return len(raw)-1
    for v,w in edges:
        a,b=coordinate(t),coordinate(t)
        clauses[v].append(a)
        clauses[w].append(b)
        clauses.append([a,b])
    for v,activity in enumerate(activities):
        degree=len(clauses[v])
        scale=times([q]*degree)
        if degree==3:
            assert scale==activity==1
        else:
            e=coordinate(mul(activity,mul(scale,scale)))
            z=coordinate(0)  # y=0 means physical Boolean coordinate z=1
            clauses[v].append(e)
            clauses.extend(([e,z],[z]))
    assert all(1<=len(c)<=3 for c in clauses)
    assert all(sum(i in c for c in clauses)==2 for i in range(len(raw)))
    factors=raw+[(tuple(c),[0]+[1]*((1<<len(c))-1)) for c in clauses]
    return partition(factors),times([k]*len(edges))


def main():
    for joined in (False,True):
        factors=[((0,1),(0,1,2,3)), ((2,3),(3,2,1,0)), ((0,),(1,2))]
        if joined:
            factors.append(((1,2),(1,0,3,1)))
        expected=0
        for bits in product(range(2),repeat=4):
            expected ^= times(tab[sum(bits[u]<<j for j,u in enumerate(scope))]
                              for scope,tab in factors)
        assert partition(factors)==expected
    R=[[1,1],[1,0]]
    assert matmul(matmul(R,R),R)==[[1,0],[0,1]]
    for t in (2,3):
        q=mul(t,mul(1^t,1^t))
        k=1^mul(t,t)
        T=[[1,t],[t,t]]
        expect=[[mul(k,times([q]*(i+j))) if R[i][j] else 0 for j in range(2)]
                for i in range(2)]
        assert times([q]*3)==1 and q!=1 and matmul(T,T)==expect
        # Source phi=(NOT x OR y). Copy x by length-three equality; place
        # complementary literal at site 4 via triangle on sites 3,4,5.
        edges=[(0,1),(1,2),(2,3),(3,4),(3,5),(4,5),(4,6),(7,6)]
        for x,y in product(range(4),repeat=2):
            actual,scale=physical(edges,[x,1,1,1,1,1,1,y],t)
            desired=0
            for a,b in product(range(2),repeat=2):
                if not a or b:
                    desired ^= times([x]*a+[y]*b)
            assert actual==mul(scale,desired)
    print('Both primitive specializations, physical read-two clauses, and all source activity pairs passed.')


if __name__=='__main__':
    main()
