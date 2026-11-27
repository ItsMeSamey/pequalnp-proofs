"""Last-reset decision for a complete deterministic width-two side and weighted side."""
from boolean_value_automata import apply, dot, insert


def validate(program,order):
    dims,start,layers,final=program
    n=len(layers)
    if sorted(order)!=list(range(n)) or len(dims)!=n+1 or min(dims)<0:
        raise ValueError('invalid order or dimensions')
    if start<0 or start.bit_length()>dims[0] or final<0 or final.bit_length()>dims[-1]:
        raise ValueError('invalid endpoint')
    for i,layer in enumerate(layers):
        if len(layer)!=2: raise ValueError('need both input transitions')
        for rows in layer:
            if len(rows)!=dims[i] or any(row<0 or row.bit_length()>dims[i+1] for row in rows):
                raise ValueError('invalid matrix')


def value(program,order,x):
    _,state,layers,final=program
    for v,layer in zip(order,layers): state=apply(state,layer[(x>>v)&1])
    return dot(state,final)


def solve(det,first,weighted,other):
    validate(det,first); validate(weighted,other)
    dims,start,dl,accept=det
    wd,ws,wl,wf=weighted
    if len(first)!=len(other):raise ValueError('orders use different bit sets')
    if min(dims)<1 or max(dims)>2 or start.bit_count()!=1 or any(
        row.bit_count()!=1 for layer in dl for rows in layer for row in rows
    ):
        return {'status':'skip','reason':'requires complete deterministic width at most two'}
    maps=[]
    for layer in dl:
        ab=[]
        for rows in layer:
            b=rows[0].bit_length()-1
            # Duplicate state zero's transition at a padded, unreachable state.
            dest=rows[-1].bit_length()-1
            ab.append((b^dest,b))
        maps.append(ab)
    n=len(first)
    cost={'branches':0,'feasible_pin_systems':0,'candidate_rows':0,'max_basis':0}
    if not accept:return {'status':'unsat','cost':cost}
    for reset in range(-1,n):
        cost['branches']+=1
        permissions=[3]*n
        pmask=0
        constant=start.bit_length()-1 if reset<0 else 0
        for i in range(max(reset,0),n):
            v=first[i]
            permissions[v]=sum(1<<x for x in (0,1) if maps[i][x][0]==int(i!=reset))
            b0=maps[i][0][1]; b1=maps[i][1][1]
            constant^=b0
            pmask|=(b0^b1)<<v
        if not all(permissions):continue
        cost['feasible_pin_systems']+=1
        # Two contiguous weighted row blocks indexed by accumulated parity.
        current=[(ws,0)] if ws else []
        for i,v in enumerate(other):
            if not current:break
            basis={}; following=[]
            mask=(1<<wd[i])-1
            for x in (0,1):
                if not (permissions[v]>>x)&1:continue
                rows=wl[i][x]
                for state,word in current:
                    cost['candidate_rows']+=1
                    low=apply(state&mask,rows)
                    high=apply(state>>wd[i],rows)
                    if x and (pmask>>v)&1: low,high=high,low
                    nxt=low|(high<<wd[i+1])
                    if insert(basis,nxt,0): following.append((nxt,word|(x<<v)))
            current=following
            cost['max_basis']=max(cost['max_basis'],len(current))
        for state,word in current:
            yes=0
            for parity in (0,1):
                if (accept>>(constant^parity))&1:
                    yes^=dot(state>>(parity*wd[-1]),wf)
            if yes:
                if not (value(det,first,word) and value(weighted,other,word)):
                    raise AssertionError('physical intersection witness mismatch')
                return {'status':'sat','witness':word,'cost':cost}
    return {'status':'unsat','cost':cost}
