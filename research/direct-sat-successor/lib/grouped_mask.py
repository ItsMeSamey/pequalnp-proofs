"""Certified equal-column grouping with exact Gauss sums and original raw pinning."""
from itertools import chain


def bits(x):
    while x:
        b=x&-x
        yield b.bit_length()-1
        x^=b


def certificate(n,gates,output):
    if n<0 or not 0<=output<1<<(1+n+len(gates)):
        raise ValueError("invalid output or dimension")
    columns=[0]*len(gates)
    for j,pair in enumerate(gates):
        if len(pair)!=2 or any(not 0<=r<1<<(1+n+j) for r in pair):
            raise ValueError("invalid or noncausal input")
        for side,row in enumerate(pair):
            for i in bits(row>>(1+n)):
                columns[i]|=1<<(2*j+side)
    groups={}
    for i,col in enumerate(columns):
        groups.setdefault(col,[]).append(i)
    ell=0
    pieces=[]
    number=1
    for col,ids in sorted(groups.items()):
        split=(len(ids)+1)//2 if col else len(ids)
        ones=sum(1<<i for i in ids[:split])
        zeros=sum(1<<i for i in ids[split:])
        ell|=ones
        if col:
            pieces.append((ones,zeros))
            number*=(1<<split)+(1<<(len(ids)-split))-1
    return groups,pieces,ell,number


def estimate(n,gates,output):
    return (n+1)*certificate(n,gates,output)[3]


def affine(w):
    return ({0} if w&1 else set())|{1<<j for j in bits(w>>1)}


def multiply(P,Q):
    out=set()
    for a in P:
        for b in Q:
            out.symmetric_difference_update([a|b])
    return out


def gauss(phase,N,eq):
    rows={}
    for a,c in eq:
        while a:
            i=a.bit_length()-1
            if i not in rows:
                rows[i]=a,c
                break
            b,v=rows[i]
            a^=b
            c^=v
        else:
            if c:
                return 0
    forms=[]
    dim=0
    for i in range(N):
        if i not in rows:
            forms.append({1<<dim})
            dim+=1
        else:
            b,c=rows[i]
            f={0} if c else set()
            for j in bits(b^(1<<i)):
                f^=forms[j]
            forms.append(f)
    Q=set()
    for m in phase:
        term={0}
        for i in bits(m):
            term=multiply(term,forms[i])
        Q^=term
    scale=1
    while True:
        uv=next((v for v in Q if v.bit_count()==2),None)
        if uv is None:
            return 0 if Q-{0} else (-1 if 0 in Q else 1)*scale*(1<<dim)
        u=uv&-uv
        v=uv^u
        A={a^u for a in Q if a!=uv and a&u}
        B={a^v for a in Q if a!=uv and a&v}
        Q={m for m in Q if not m&uv}^multiply(A,B)
        dim-=2
        scale*=2


def subsets(mask,include_empty):
    x=mask
    while x:
        yield x
        x=(x-1)&mask
    if include_empty:
        yield 0


def masks(pieces):
    # Product of local iterators without materializing their powersets.
    if not pieces:
        yield 0
        return
    def local(i):
        a,b=pieces[i]
        return chain(subsets(a,True),subsets(b,False))
    stack=[local(0)]
    prefixes=[0]
    while stack:
        choice=next(stack[-1],None)
        if choice is None:
            stack.pop()
            prefixes.pop()
        elif len(stack)==len(pieces):
            yield prefixes[-1]|choice
        else:
            prefixes.append(prefixes[-1]|choice)
            stack.append(local(len(stack)))


def solve(n,gates,output,*,budget):
    if not isinstance(budget,int) or budget<0:
        raise ValueError("invalid mask budget")
    groups,pieces,ell,num=certificate(n,gates,output)
    cost=dict(mask_bound=num*(n+1),masks_per_count=num,masks=0,counts=0,
              groups=[dict(effect=c,indices=v) for c,v in sorted(groups.items())],sign_word=ell,budget=budget)
    if budget<cost['mask_bound']:
        return dict(status='skip',cost=cost)
    m=len(gates)
    gauge=((1<<m)-1)^ell^(output>>(n+1))
    P=affine(output)
    for i in bits(gauge):
        a,b=gates[i]
        P^={1<<(n+i)}^multiply(affine(a),affine(b))
    def count(pins):
        total=0
        cost['counts']+=1
        for U in masks(pieces):
            eq=pins.copy()
            Q=P.copy()
            for i,(a,b) in enumerate(gates):
                z=1<<(n+i)
                if U>>i&1:
                    eq.extend([(a>>1,1^(a&1)),(b>>1,1^(b&1))])
                    Q^={0,z}
                else:
                    eq.append((z,0))
            cost['masks']+=1
            total+=gauss(Q,n+m,eq)
        value,rem=divmod((1<<(n-len(pins)))-total,2)
        assert not rem and value>=0
        return value
    original=count([])
    cost['accepting_assignments']=original
    if not original:
        return dict(status='unsat',cost=cost)
    pins=[]
    witness=0
    for j in range(n):
        bit=int(count(pins+[(1<<j,0)])==0)
        pins.append((1<<j,bit))
        witness|=bit<<j
    word=1|(witness<<1)
    for j,(a,b) in enumerate(gates):
        word|=(((word&a).bit_count()&1)&((word&b).bit_count()&1))<<(1+n+j)
    if not (output&word).bit_count()&1:
        raise AssertionError("witness fails original circuit")
    return dict(status='sat',witness=witness,cost=cost)
