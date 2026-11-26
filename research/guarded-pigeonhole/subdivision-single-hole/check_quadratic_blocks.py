from itertools import product


def signed_counts(m):
    size=2*m+1
    counts=[0]*(1<<size)
    for x in range(1<<size):
        h=x&1
        for i in range(m):
            u=x>>(1+2*i)&1
            v=x>>(2+2*i)&1
            if u*v or (u^h)*v or u*(v^h^1):
                break
        else:
            counts[x]=1
    step=1
    while step<len(counts):
        for base in range(0,len(counts),2*step):
            for t in range(base,base+step):
                lo,hi=counts[t],counts[t+step]
                counts[t],counts[t+step]=lo+hi,lo-hi
        step*=2
    for mask,count in enumerate(counts):
        b=any(mask>>(1+2*i)&1 for i in range(m))
        e=any(mask>>(2+2*i)&1 for i in range(m))
        expected=(1<<m)*(int(not e)+(-1 if mask&1 else 1)*int(not b))
        assert count==expected


for m in range(1,7):
    signed_counts(m)
print('Full signed portfolios passed for module counts 1 through 6.')
