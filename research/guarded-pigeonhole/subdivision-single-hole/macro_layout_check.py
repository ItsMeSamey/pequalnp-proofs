"""Normal-space tree DP with implicit Gaussian leaf summation and unsigned reconstruction."""
from fractions import Fraction
from itertools import combinations,product
from random import Random

from macro_fourier import ZERO,ONE,affine_domain,leaf_expansion,private_sum,restrict,evaluate
from truth_projection import echelon,coordinates,kernel,index


def basis(forms):
    return tuple(v for v,_ in echelon(forms).values())


def intersect(U,V,n):
    return tuple(kernel(kernel(U,n)+kernel(V,n),n))


def point(forms,state,n):
    system=affine_domain((v,state>>i&1) for i,v in enumerate(forms))
    if system is None:return None
    return sum((row&-row)*rhs for row,rhs in system)


def marginal(expansion,normal_dim,ambient_dim,pins):
    """Work in local evaluation coordinates plus arbitrary dummy ambient coordinates."""
    total=Fraction()
    for (domain,phase),weight in expansion.items():
        fixed=affine_domain((*domain,*pins))
        if fixed is None:continue
        free=(1<<ambient_dim)-1
        for row,_ in fixed:free^=row&-row
        amplitude,extra,sign=private_sum(restrict(phase,fixed),free)
        assert not extra and sign in (ZERO,ONE)
        total+=weight*amplitude*(-1 if sign else 1)
    total/=1<<(ambient_dim-normal_dim)
    assert total.denominator==1
    return int(total)


def run(n,leaves,tree,recover=False):
    """A leaf is (independent normal basis, private bit count, guards, local character)."""
    if recover and any(ch for _,_,_,ch in leaves):raise ValueError('reconstruction requires unsigned factors')
    nodes={}
    visit=[]
    def span(t):
        if isinstance(t,int):
            forms=leaves[t][0]
            if len(basis(forms))!=len(forms):raise ValueError('dependent normal basis')
            visit.append(t)
        else:forms=span(t[0])+span(t[1])
        nodes[t]={'U':basis(forms)}
        return nodes[t]['U']
    full=span(tree)
    if sorted(visit)!=list(range(len(leaves))):raise ValueError('tree must partition the leaves')

    def build(t,outside):
        rec=nodes[t]
        B=intersect(rec['U'],outside,n)
        rec['B']=B
        if isinstance(t,int):
            forms,k,guards,ch=leaves[t]
            expand=leaf_expansion(len(forms),(k,guards,ch))
            piv=echelon(forms)
            local=[coordinates(v,piv) for v in B]
            rec.update(expansion=expand,local=local)
            rec['table']={x:marginal(expand,len(forms),n,[(v,x>>i&1) for i,v in enumerate(local)])
                          for x in range(1<<len(B))}
            return
        left,right=t
        build(left,basis(outside+nodes[right]['U']))
        build(right,basis(outside+nodes[left]['U']))
        L,R=nodes[left],nodes[right]
        forms=L['B']+R['B']
        rec.update(table={},back={})
        for a,wa in L['table'].items():
            for b,wb in R['table'].items():
                if not wa or not wb:continue
                shared=point(forms,a|(b<<len(L['B'])),n)
                if shared is None:continue
                parent=index(B,shared)
                rec['table'][parent]=rec['table'].get(parent,0)+wa*wb
                if recover:rec['back'].setdefault(parent,(a,b))
    build(tree,())
    count=nodes[tree]['table'].get(0,0)*(1<<(n-len(full)))
    if not recover or not count:return count,None

    eqs=[]
    private={}
    def unpack(t,state):
        rec=nodes[t]
        if not isinstance(t,int):
            a,b=rec['back'][state]
            unpack(t[0],a)
            unpack(t[1],b)
            return
        forms,k,guards,_=leaves[t]
        pins=[(v,state>>i&1) for i,v in enumerate(rec['local'])]
        chosen=0
        for i in range(len(forms)):
            b=int(not marginal(rec['expansion'],len(forms),n,pins+[(1<<i,0)]))
            pins.append((1<<i,b))
            chosen|=b<<i
        eqs.extend((v,chosen>>i&1) for i,v in enumerate(forms))
        # Expand only the guard subset. Pin private bits inside this leaf; no global re-layout.
        phases=[ZERO]
        for g in guards:phases.extend([phase^g for phase in phases])
        from collections import Counter
        weights=Counter(phases)
        local_exp={((),phase):Fraction(weight,len(phases)) for phase,weight in weights.items()}
        d=len(forms)+k
        fixed=[(1<<i,chosen>>i&1) for i in range(len(forms))]
        z=0
        for j in range(k):
            bit=1<<(len(forms)+j)
            value=int(not marginal(local_exp,d,d,fixed+[(bit,0)]))
            fixed.append((bit,value))
            z|=value<<j
        private[t]=z
    unpack(tree,0)
    normal_rows=[v for v,_ in eqs]
    x=point(normal_rows,sum(b<<i for i,(_,b) in enumerate(eqs)),n)
    assert x is not None
    for i,(forms,k,guards,_) in enumerate(leaves):
        assert not any(evaluate(g,index(forms,x)|(private[i]<<len(forms))) for g in guards)
    return count,(x,private)


def fold(items):
    if len(items)==1:return items[0]
    half=len(items)//2
    return fold(items[:half]),fold(items[half:])


def coloring(vertices,edges):
    leaves=[((1<<(2*i),1<<(2*i+1)),0,(frozenset({3}),),ZERO) for i in range(vertices)]
    for a,b in edges:
        forms=(1<<(2*a),1<<(2*a+1),1<<(2*b),1<<(2*b+1))
        poly=frozenset({0,1,2,4,8,5,6,9,10})
        leaves.append((forms,0,(frozenset({5}),frozenset({10}),poly),ZERO))
    n=2*vertices
    count,w=run(n,leaves,fold(list(range(len(leaves)))),True)
    expected=sum(all(z[a]!=z[b] for a,b in edges) for z in product(range(3),repeat=vertices))
    assert count==expected and bool(w)==bool(count)
    return count


if __name__=='__main__':
    rng=Random(2027)
    for _ in range(170):
        n=rng.randrange(1,6)
        leaves=[]
        for j in range(rng.randrange(1,6)):
            forms=basis(rng.getrandbits(n) for _ in range(rng.randrange(4)))
            k=rng.randrange(3)
            dim=len(forms)+k
            monos=[i for i in range(1<<dim) if i.bit_count()<=2]
            def poly():return frozenset(i for i in monos if rng.randrange(4)==0)
            guards=tuple(poly() for _ in range(rng.randrange(3)))
            leaves.append((forms,k,guards,ZERO if _%2 else poly()))
        count,w=run(n,leaves,fold(list(range(len(leaves)))),not any(ch for _,_,_,ch in leaves))
        truth=0
        for x in range(1<<n):
            weight=1
            for forms,k,guards,ch in leaves:
                weight*=sum(
                    (-1)**evaluate(ch,a) for z in range(1<<k)
                    for a in [index(forms,x)|(z<<len(forms))]
                    if all(not evaluate(g,a) for g in guards))
            truth+=weight
        assert count==truth
    assert coloring(5,[(0,1),(1,2),(2,3),(3,4)])==48
    assert coloring(3,[(0,1),(1,2),(0,2)])==6
    assert coloring(4,list(combinations(range(4),2)))==0
    print('170 rotated-normal signed/unsigned tests; path=48, triangle=6, K4=0.')
