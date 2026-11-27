"""Original B2 DAGs; truth bit 2*a+b, last gate output; exact local recompilation."""
from random import Random
from original_dag_portfolio import compact,table


def benchmark(blocks,suffix):
    q=2*blocks
    original=[]
    for i in range(blocks):
        for c in (1,2,4):
            original.append((c,2*i,2*i+1))
    # Suffix refers to encoded coordinates 0..3b-1 followed by its own gates.
    original.extend((c,q+a,q+b) for c,a,b in suffix)
    original=compact(q,original)
    rewritten=[]
    def add(c,a,b):
        rewritten.append((c,a,b))
        return q+len(rewritten)-1
    # Store the truth table of every wire confined to a single block.
    infos=[(i//2,12 if i%2==0 else 10) for i in range(q)]
    wires=list(range(q))
    cache={}
    def local(j,t):
        key=j,t
        if key not in cache:
            cache[key]=2*j if t==12 else 2*j+1 if t==10 else add(t,2*j,2*j+1)
        return cache[key]
    affine_hits=local_hits=0
    for c,a,b in original:
        left,right=infos[a],infos[b]
        if left and right and left[0]==right[0]:
            j=left[0]
            t=sum((c>>(2*(left[1]>>v&1)+(right[1]>>v&1))&1)<<v for v in range(4))
            local_hits+=1
            affine_hits+=t.bit_count()%2==0
            infos.append((j,t));wires.append(local(j,t))
        else:
            infos.append(None);wires.append(add(c,wires[a],wires[b]))
    if wires[-1]!=q+len(rewritten)-1:add(12,wires[-1],wires[-1])
    rewritten=compact(q,rewritten)
    assert table(q,original)==table(q,rewritten)
    return dict(raw=q,live_before=len(original),live_after=len(rewritten),local=local_hits,
                local_affine=affine_hits,ones=table(q,original).bit_count())


def build(b,kind):
    g=[]
    def add(c,a,d):
        g.append((c,a,d))
        return 3*b+len(g)-1
    if kind=='hostile':
        last=0
        for j in range(1,b):last=add(8,last,3*j)
        return g
    if kind=='interleaved':
        seq=[3*j+i for i in range(3) for j in range(b)]
        last=seq[0]
        for i,operand in enumerate(seq[1:]):
            last=add((6,8,14,7,11)[i%5],last,operand)
        return g
    rng=Random(108)
    h=[]
    for i in range(b):
        a=add(14,3*i,3*i+1)  # complement of first raw coordinate
        d=add(6,3*i+1,3*i+2) # raw parity
        if kind=='seeded':
            a=add(rng.randrange(16),a,d)
        h.extend([a,d])
    root=h[0]
    for i in [*range(2,len(h),2),*range(1,len(h),2)]:
        root=add(rng.choice((1,2,4,6,7,8,9,11,13,14)),root,h[i])
    return g


if __name__=='__main__':
    for kind in ('positive','seeded','interleaved','hostile'):
        result=benchmark(4,build(4,kind))
        print(kind,result)
        if kind=='hostile':
            assert result['live_before']==result['live_after']==7 and result['ones']==1
        elif kind=='interleaved':
            assert result['live_before']==result['live_after']==23
        else:assert result['live_after']<result['live_before']
