"""Compare the component-kernel recognition DP to all labelled-column partitions."""
from random import Random

def span(cols):
    out={0}
    for c in cols:out.update(x^c for x in list(out))
    return out

def partition_recognition(cols):
    m=len(cols)
    piv={}
    parent=list(range(m))
    def root(j):
        while j!=parent[j]:
            j=parent[j]
        return j
    for j,c in enumerate(cols):
        tag=1<<j
        while c:
            bit=c.bit_length()-1
            if bit not in piv:
                piv[bit]=c,tag
                break
            x,t=piv[bit]
            c^=x;tag^=t
        if not c:
            for k in range(j):
                if tag>>k&1:parent[root(k)]=root(j)
    by={}
    for j,c in enumerate(cols):by.setdefault(root(j),[]).append(c)
    components=list(by.values())
    universe=frozenset(range(16))
    states={(universe,universe)}
    for j in range(len(components)):
        rest=span(v for i,comp in enumerate(components) if i!=j for v in comp)
        kernel=universe & rest
        states={(x, y&kernel) for x,y in states}|{(x&kernel,y) for x,y in states}
    return any(len(a)==len(b)==2 for a,b in states)

def exhaustive(cols):
    n=len(cols)
    for mask in range(1<<(n-1)):
        a=span(c for j,c in enumerate(cols) if mask>>j&1)
        b=span(c for j,c in enumerate(cols) if not(mask>>j&1))
        if len(a&set(range(16)))!=2 or len(b&set(range(16)))!=2:continue
        if len({c>>4 for c in a}&{c>>4 for c in b})==4:return True
    return False

def main():
    rng=Random(922044)
    yes=no=0
    for i in range(200):
        left=[16,32,1];right=[20,40,2]
        cols=left+right
        if i%2:
            # Densify each summand, without linking the prescribed split.
            for side in (left,right):
                for j in range(rng.randrange(3)):cols.append(rng.choice(sorted(span(side))))
        else:
            cols += [rng.randrange(64) for _ in range(rng.randrange(1,5))]
        assert set(range(16))<=span(cols)
        p=partition_recognition(cols)
        assert p==exhaustive(cols)
        yes+=p;no+=not p
    print(yes,"recognized;",no,"rejected")
if __name__=='__main__': main()
