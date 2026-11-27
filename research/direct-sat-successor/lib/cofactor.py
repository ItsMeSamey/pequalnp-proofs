"""Scalar-preserving conditional cofactor on an indexed XOR-AND presentation."""
def translate(form, refs):
    result=0
    while form:
        bit=form & -form
        result ^= refs[bit.bit_length()-1]
        form ^= bit
    return result

def compact(n, gates, output):
    needed=output
    keep=[]
    for j in reversed(range(len(gates))):
        if needed >> (n+1+j) & 1:
            a,b=gates[j]
            needed |= a|b
            keep.append(j)
    keep.reverse()
    refs=[1<<j for j in range(n+1)]+[0]*len(gates)
    new=[]
    for j in keep:
        a,b=gates[j]
        refs[n+j+1]=1<<(n+len(new)+1)
        new.append((translate(a,refs),translate(b,refs)))
    return new,translate(output,refs)

def rewrite(n, gates, output, gate, selector_side, pivot):
    """pivot is a signal index, 1..n raw, n+1 onward producer; 0 is constant."""
    u,v=gates[gate][::1 if selector_side==0 else -1]
    assert pivot>0 and u>>pivot&1
    new=[]; known={}
    def emit(a,b):
        if a==0 or b==0 or a^b==1:return 0
        if a==1 or a==b:return b
        if b==1:return a
        key=tuple(sorted((a,b)))
        if key not in known:
            known[key]=1<<(n+1+len(new));new.append(key)
        return known[key]
    originals=[1<<i for i in range(n+1)]
    for a,b in gates[:gate]:
        originals.append(emit(translate(a,originals),translate(b,originals)))
    replace=translate(1^u^(1<<pivot),originals)
    local=originals[:n+1]
    if pivot<=n:local[pivot]=replace
    for j,(a,b) in enumerate(gates[:gate],n+1):
        if j==pivot: local.append(replace)
        elif u>>j&1: local.append(originals[j]) # frozen original, not re-evaluated
        else: local.append(emit(translate(a,local),translate(b,local)))
    originals.append(emit(translate(u,originals),translate(v,local)))
    for a,b in gates[gate+1:]:
        originals.append(emit(translate(a,originals),translate(b,originals)))
    return compact(n,new,translate(output,originals))

def value(n,gates,output,x):
    bits=1|(x<<1)
    for j,(a,b) in enumerate(gates):
        bit=((a&bits).bit_count() & (b&bits).bit_count())&1
        bits |= bit<<(n+1+j)
    return (bits&output).bit_count()&1
