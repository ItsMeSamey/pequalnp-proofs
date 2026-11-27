from itertools import product
from random import Random
from multi_order_closure import solve, value, Meter


def matching(n,edges):
    used=set()
    order=[]
    layers=[]
    for x,y in edges:
        assert x not in used and y not in used
        used.update((x,y))
        order.extend((x,y))
        layers.extend([((1,0),(2,0)), ((1,1),(1,0))])
    for x in sorted(set(range(n))-used):
        order.append(x)
        layers.append(((1,2),(1,2)))
    return order,([2]*(n+1),1,layers,1)


def mgg(t):
    edges=set()
    for x,y in product(range(t),repeat=2):
        a=x*t+y
        for u,v in ((x+2*y,y),(x+2*y+1,y),(x,y+2*x),(x,y+2*x+1)):
            b=(u%t)*t+v%t
            if a!=b: edges.add(tuple(sorted((a,b))))
    colors=[]
    for edge in sorted(edges):
        for group,used in colors:
            if used.isdisjoint(edge): break
        else:
            group,used=[],set()
            colors.append((group,used))
        group.append(edge)
        used.update(edge)
    return [matching(t*t,g) for g,_ in colors], min(edges)


def dense_transform(f):
    # Conjugate every 2-state layer by invertible, nondiagonal T=T⁻¹.
    order,(w,s,ls,e)=f
    def row(x): return x ^ ((x&1)<<1)
    def mat(a): return (row(a[0]^a[1]), row(a[1]))
    return order,(w,row(s),[tuple(mat(v) for v in pair) for pair in ls], e ^ ((e>>1)&1))


def main():
    zero=([0],([1,1],1,[((0,),(0,))],1))
    onebit=([0],([1,1],1,[((0,),(1,))],1))
    for mode in ("meet","majority"):
        for make in (list,tuple,iter):
            for f in (zero,onebit):
                r=solve(1,make([f,f]),mode=mode)
                assert r["status"]==("unsat" if f is zero else "sat")
                if f is onebit:
                    assert r["witness"]==1 and value(f,1,Meter(10))
    for t in (2,4):
        fs,edge=mgg(t)
        fs=list(map(dense_transform,fs))
        for mode in ("meet","majority"):
            for pins,expected in (({edge[0]:1},"sat"),(dict.fromkeys(edge,1),"unsat")):
                a=solve(t*t,fs,mode=mode,pins=pins,budget=12000000)
                assert a["status"]==expected,a
                print(t*t,len(fs),mode,expected,a["work"])
    rng=Random(48)
    for _ in range(60):
        n=3
        fs=[]
        for j in range(2):
            order=rng.sample(range(n),n)
            p=([2]*4,rng.randrange(1,4),[[tuple(rng.randrange(4) for _ in range(2)) for b in (0,1)] for i in order],rng.randrange(1,4))
            fs.append((order,p))
        models=[x for x in range(8) if all(value(f,x,Meter(10000)) for f in fs)]
        for mode in ('meet','majority'):
            result=solve(n,fs,mode=mode)
            if result['status']=='skip':
                words=result['counterexample']
                f=fs[result['factor']]
                out=words[0]&words[1] if mode=='meet' else (words[0]&words[1])|(words[0]&words[2])|(words[1]&words[2])
                assert all(value(f,x,Meter(10000)) for x in words) and not value(f,out,Meter(10000))
            else:
                assert (result['status']=='sat')==bool(models)
                if models: assert result['witness'] in models
    print('120 random dispatch comparisons; cap status',solve(4,mgg(2)[0],width_cap=1)['status'])


if __name__=='__main__': main()
