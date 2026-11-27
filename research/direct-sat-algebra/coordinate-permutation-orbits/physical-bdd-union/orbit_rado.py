"""Canonical four-position orbit subcube decision with original generator recipes."""
from itertools import combinations
from math import isqrt
from rado_matroid import kernel

def reduce_row(eq,v,c=0):
    for p in sorted(eq, reverse=True):
        if v>>p&1:
            w,b=eq[p]
            v,c=v^w,c^b
    return v,c

def insert(eq,v,c):
    v,c=reduce_row(eq,v,c)
    if v:
        eq[v.bit_length()-1]=v,c
    return bool(v or not c)

def parity(x):
    return x.bit_count()&1

def move(perm,word):
    ans=0
    while word:
        b=word&-word
        ans |= 1<<perm[b.bit_length()-1]
        word ^= b
    return ans

def solve(rotation,flip,start,zero,ones=0,*,assignment_cap=None):
    rotation,flip=tuple(rotation),tuple(flip)
    dim=len(rotation)
    if assignment_cap is not None and (type(assignment_cap)!=int or assignment_cap<0):
        raise ValueError('nonnegative assignment cap required')
    if any(type(x)!=int or x<0 or x>>dim for x in (start,zero,ones)):
        raise ValueError('invalid physical bit mask')
    m=(1+isqrt(1+2*dim))//2
    if m%2!=1 or 2*m*(m-1)!=dim or len(flip)!=dim:
        return dict(status='skip',reason='noncanonical dimensions')
    pairs=list(combinations(range(m),2))
    ids={pair:4*k for k,pair in enumerate(pairs)}
    initial=0
    for k,(u,v) in enumerate(pairs):
        t=ids[tuple(sorted(((u+1)%m,(v+1)%m)))]
        initial |= 1<<(4*k)
        for a in range(4):
            i=4*k+a
            if (type(rotation[i])!=int or type(flip[i])!=int or
                rotation[i]!=t+((a&1)<<1)+(a>>1) or flip[i]!=4*k+(a^int(u==0 or v==0))):
                return dict(status='skip',reason='noncanonical generators')
    if initial!=start:
        return dict(status='skip',reason='noncanonical start')
    cost=dict(vertices=m,sites=dim,deficiency=None,intersection_calls=0,
              component_ranks=[],assignments=0,restarts=0,replay_moves=0)
    def no():
        return dict(status='unsat',cost=cost)
    eq={}
    forbids=[]
    for k,(u,v) in enumerate(pairs):
        absent=(zero>>(4*k))&15
        high=(ones>>(4*k))&15
        if high.bit_count()>1:
            return no()
        allowed=[a for a in range(4) if (not high or high==1<<a) and not (absent>>a&1)]
        if not allowed:
            return no()
        lo=(1<<(2*u))|(1<<(2*v))
        hi=lo<<1
        if len(allowed)==3:
            bad=next(a for a in range(4) if a not in allowed)
            forbids.append((lo,hi,bad))
        else:
            for s,mask in ((1,lo),(2,hi),(3,lo^hi)):
                vals={parity(s&a) for a in allowed}
                if len(vals)==1 and not insert(eq,mask,vals.pop()):
                    return no()
    while True:
        rows=[]
        for lo,hi,bad in forbids:
            a,x=reduce_row(eq,lo,bad&1)
            b,y=reduce_row(eq,hi,bad>>1)
            if (not a and x) or (not b and y) or (a==b and x!=y):
                continue
            if not (a or b):
                return no()
            if not a or not b or a==b:
                mask,value=(a,x) if a else (b,y)
                if not insert(eq,mask,1^value):
                    return no()
                cost['restarts']+=1
                break
            rows.append((a,b,x|(y<<1)))
        else:
            break
    planes=[(a,b) for a,b,_ in rows]
    components,outside,loss,calls=kernel(planes)
    cost.update(deficiency=loss,intersection_calls=calls,nonlinear=len(planes))
    for i,s in outside.items():
        a,b,bad=rows[i]
        mask=(a if s&1 else 0)^(b if s&2 else 0)
        if not insert(eq,mask,1^parity(s&bad)):
            raise AssertionError('outside extension inconsistent')
    for comp in components:
        basis={}
        for i in comp:
            for mask in planes[i]:
                insert(basis,mask,0)
        basis_rows=[mask for mask,_ in basis.values()]
        rank=len(basis_rows)
        cost['component_ranks'].append(rank)
        dual={row.bit_length()-1:(row,1<<j) for j,row in enumerate(basis_rows)}
        local=[]
        for i in comp:
            a,b,bad=rows[i]
            left,x=reduce_row(dual,a)
            right,y=reduce_row(dual,b)
            if left or right:
                raise AssertionError('core coordinate extraction')
            local.append((x,y,bad))
        for z in range(1<<rank):
            if assignment_cap is not None and cost['assignments']>=assignment_cap:
                return dict(status='skip',reason='core assignment cap',cost=cost)
            cost['assignments']+=1
            if all((parity(x&z)|(parity(y&z)<<1))!=bad for x,y,bad in local):
                for j,row in enumerate(basis_rows):
                    if not insert(eq,row,(z>>j)&1):
                        raise AssertionError('core extension inconsistent')
                break
        else:
            return no()
    colors=0
    for p,(mask,c) in sorted(eq.items()):
        colors |= (parity(mask&colors)^c)<<p
    recipe=tuple(j for j in range(2*m) if colors>>(2*(j%m)+(j%2))&1)
    state=start
    for j in recipe:
        for _ in range((-j)%(2*m)):
            state=move(rotation,state)
            cost['replay_moves']+=1
        state=move(flip,state)
        cost['replay_moves']+=1
        for _ in range(j):
            state=move(rotation,state)
            cost['replay_moves']+=1
    if state&zero or state&ones!=ones:
        raise AssertionError('original orbit witness rejected')
    return dict(status='sat',word=recipe,state=state,cost=cost)
