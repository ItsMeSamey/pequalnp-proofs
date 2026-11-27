"""Exact sparse ANF chart-image decision in the supplied assignment-variable order."""
from image_solver import normalize
from recognizer import bit_indices,tag_at
from fixed_height import prior

def basis(vectors):
    rows={}
    for x in vectors:
        for i in sorted(rows,reverse=True):
            if x>>i&1: x ^= rows[i]
        if not x: continue
        i=x.bit_length()-1
        for j,old in list(rows.items()):
            if old>>i&1: rows[j]=old^x
        rows[i]=x
    return tuple(rows[i] for i in sorted(rows))

def intersection(left,right):
    pivots={}
    common=[]
    for x,y in [(v,0) for v in right]+[(v,v) for v in left]:
        while x:
            i=x.bit_length()-1
            if i not in pivots:
                pivots[i]=(x,y)
                break
            row,trace=pivots[i]
            x ^= row
            y ^= trace
        if not x and y: common.append(y)
    return basis(common)

def substitute(poly,bit,value):
    result=set()
    for m in poly:
        if not m&bit: result.symmetric_difference_update((m,))
        elif value: result.symmetric_difference_update((m^bit,))
    return frozenset(result)

def tag_tests(columns,encoder,d):
    tests=[]
    for k,b,_ in columns:
        pair=[]
        for a in range(2):
            terms={0} if b>>a&1 else set()
            for coord in bit_indices(k):
                terms.symmetric_difference_update(encoder[a*d+coord])
            pair.append(frozenset(terms))
        tests.append(tuple(pair))
    return tests

def residual_rank(tests,unfinished,prefix):
    coordinates={}
    vectors={}
    for idx in unfinished:
        for a,poly in enumerate(tests[idx]):
            for term in poly:
                before=term&prefix
                if not before: continue
                label=(idx,a,term^before)
                pos=coordinates.setdefault(label,len(coordinates))
                vectors[before]=vectors.get(before,0)^(1<<pos)
    return len(basis(vectors.values()))

def solve(columns,d,n,encoder):
    if min(d,n)<0: raise ValueError("negative dimension")
    columns=tuple(columns)
    if any(not (0<=k<1<<d and 0<=b<4 and 0<=h<4) for k,b,h in columns):
        raise ValueError("invalid physical coordinates")
    encoder=tuple(normalize(poly,n) for poly in encoder)
    if len(encoder)!=2*d: raise ValueError("invalid chart size")
    tests=tag_tests(columns,encoder,d)
    stages=[max((m.bit_length() for f in pair for m in f),default=0) for pair in tests]
    physical=[k<<2|h for k,b,h in columns]
    pending=list(range(len(columns)))
    states={(tuple(tests),()):0}
    bounds=[]
    for stage in range(n+1):
        bit=(1<<(stage-1)) if stage else 0
        positions=[i for i,idx in enumerate(pending) if stages[idx]==stage]
        later=[i for i,idx in enumerate(pending) if stages[idx]>stage]
        remaining=[pending[i] for i in later]
        inside=basis(v for i,v in enumerate(physical) if stages[i]<=stage)
        outside=basis([1,2]+[physical[i] for i in remaining])
        seam=intersection(inside,outside)
        new={}
        for (labels,current),prefix in states.items():
            for value in (0,1) if stage else (0,):
                reduced=tuple(tuple(substitute(f,bit,value) for f in pair) for pair in labels)
                active=[physical[pending[i]] for i in positions if not any(reduced[i])]
                boundary=intersection(basis(current+tuple(active)),seam)
                state=(tuple(reduced[i] for i in later),boundary)
                new.setdefault(state,prefix | (bit if value else 0))
        states,pending=new,remaining
        rho=residual_rank(tests,pending,(1<<stage)-1)
        bounds.append((rho,len(seam),len(states)))
    for (_,trace),assignment in states.items():
        if trace!=(1,2): continue
        g=sum((sum(m&assignment==m for m in f)%2)<<i for i,f in enumerate(encoder))
        echelon,chosen={},[]
        for idx,(k,b,h) in enumerate(columns):
            if tag_at(g,k,d)==b and prior['add'](echelon,k<<2|h): chosen.append(idx)
        return (assignment,chosen),bounds
    return None,bounds
