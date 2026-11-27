"""Boolean controls for inclusion-exclusion on normalized affine intersections."""
from itertools import product

def cases(k=5):
    """Return (name, domains, relations, output, expected_counts) tuples."""
    bits=(0,1)
    eq={(0,0),(1,1)}
    miss={(0,1),(1,0),(1,1)}
    ds={v:bits for v in 'xyzwp'}
    ds['s']=(0,)
    base=[('x','y',eq),('w','s',eq)]
    a=('x','z',miss)
    b=('y','w',miss)
    c=('y','z',miss)
    d={i:bits for i in range(2*k+1)}
    return [
        ('strict-nesting',ds,base+[a,b],'p',{0:2,1:2}),
        ('projected-duplicate',ds,base+[a,c],'p',{0:3,1:3}),
        ('three-way-cancellation',ds,base+[a,c,b],'p',{0:2,1:2}),
        ('independent-pairs',d,[(2*i,2*i+1,miss) for i in range(k)],2*k,{0:3**k,1:3**k})]

def brute_counts(domains, relations, output):
    counts={0:0,1:0}
    for row in product(*domains.values()):
        w=dict(zip(domains,row))
        if all((w[a],w[b]) in rel for a,b,rel in relations):
            counts[w[output]]+=1
    return counts
