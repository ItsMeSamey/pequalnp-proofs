from collections import Counter
def parity(v):return v.bit_count()&1
def q(k):return ((k>>0)&(k>>1)&1)^((k>>2)&(k>>3)&1)
def tag(g,k):return parity(g&15&k)|parity((g>>4)&k)<<1
def rank(xs):
    p={}
    for x in xs:
        while x:
            j=x.bit_length()-1
            if j not in p:p[j]=x;break
            x^=p[j]
    return len(p)
candidate=[(k,b) for k in range(1,16) for b in range(4) if b!=q(k)]
constraints=[(u,g) for u in range(1,16) for g in range(256)]
hits=[sum(1<<i for i,(u,g) in enumerate(constraints) if parity(u&k) and tag(g,k)==b) for k,b in candidate]
allset=(1<<len(constraints))-1
def covered(indices):
    v=0
    for i in indices:v|=hits[i]
    return v
def hist(lst):return Counter(sum(tag(g,k)==b for k,b in lst) for g in range(256))
if __name__=='__main__':
    indices=[i for i,(k,b) in enumerate(candidate) if k not in (3,8,11) and (b&1)==(q(k)^1)]
    lst=[candidate[i] for i in indices]
    assert len(candidate)==45 and len(lst)==24
    assert all(rank(k for k,b in candidate if tag(g,k)==b)==4 for g in range(256))
    assert all(rank(k for k,b in lst if tag(g,k)==b)==4 for g in range(256))
    assert all(covered(set(indices)-{i})!=allset for i in indices)
    print('full',len(candidate),hist(candidate))
    print('restriction',len(lst),hist(lst))
