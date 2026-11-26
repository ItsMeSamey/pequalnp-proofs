"""Exhaust all two-gate binary shapes up to relabeling, and all partial pinnings."""
from itertools import product


def evaluate(tree,x):
    op,*v=tree
    if op=='c': return v[0]
    if op=='x': return x[v[0]] ^ v[1]
    a,b=evaluate(v[1],x),evaluate(v[2],x)
    return (v[0]>>(2*a+b))&1


def negate(t):
    if t[0]=='c': return ('c',1-t[1])
    if t[0]=='x': return ('x',t[1],1-t[2])
    return ('gate',15^t[1],t[2],t[3])


def simple(t,pins):
    if t[0]=='c': return t
    if t[0]=='x':
        v=pins[t[1]]
        return t if v<0 else ('c',v^t[2])
    g,a,b=t[1],simple(t[2],pins),simple(t[3],pins)
    vals=[(g>>(2*(a[1] if a[0]=='c' else i)+(b[1] if b[0]=='c' else j)))&1
          for i,j in product(range(2),repeat=2)]
    if len(set(vals))==1: return ('c',vals[0])
    if vals[0]==vals[1] and vals[2]==vals[3]: return negate(a) if vals[0] else a
    if vals[0]==vals[2] and vals[1]==vals[3]: return negate(b) if vals[0] else b
    return ('gate',g,a,b)


def nodes(t):
    return 0 if t[0]!='gate' else 1+nodes(t[2])+nodes(t[3])


def main():
    assignments=list(product(range(2),repeat=3))
    total=0
    maj=tuple(int(sum(x)>=2) for x in assignments)
    for a,b,c in ((0,1,2),(0,2,1),(1,2,0),(0,0,1)):
        for f,g in product(range(16),repeat=2):
            t=('gate',f,('gate',g,('x',a,0),('x',b,0)),('x',c,0))
            assert tuple(evaluate(t,x) for x in assignments)!=maj
            for pins in product((-1,0,1),repeat=3):
                u=simple(t,pins)
                left=sum(pins[v]<0 for v in (a,b,c))
                assert nodes(u)<=max(0,left-1)
                for x in assignments:
                    original=tuple(v if p<0 else p for p,v in zip(pins,x))
                    assert evaluate(t,original)==evaluate(u,x)
                total+=1
    assert all(int(sum(x)>=2)==((x[0]&x[1]) | (x[2]&(x[0]|x[1]))) for x in assignments)
    print(total,'projected formulas checked on every completion')


if __name__=='__main__':
    main()
