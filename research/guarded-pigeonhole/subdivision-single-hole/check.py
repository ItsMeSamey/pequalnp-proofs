"""Direct image by bitset XOR translations for repeated or strict padding."""
def xor_translate(bits,mask,width,patterns):
    k=0
    while mask:
        if mask&1:
            shift=1<<k
            low=patterns[k]
            bits=((bits&low)<<shift)|((bits>>shift)&low)
        k+=1
        mask>>=1
    return bits


def check(k,strict):
    parents=[[(0,0)]]+[[(i,1),(i+1,0)] for i in range(k-1)]+[[(k-1,1)]]
    leaves=[]
    n=k
    def split(c):
        nonlocal n
        if len(c)==3:leaves.append(c);return
        if not strict:split(c+[c[0]]);return
        z=n
        n+=1
        split(c+[(z,0)])
        split(c+[(z,1)])
    for c in parents:split(c)
    occ=sum(leaves,[])
    f=[0]*len(occ)
    w=[0]*len(occ)
    t=d=0
    for j in range(n):
        indices=[i for i,(v,s) in enumerate(occ) if v==j]
        for a,b in zip(indices,indices[1:]):
            f[a]^=1<<d
            f[b]^=1<<d
            t|=(occ[a][1]^occ[b][1])<<d
            d+=1
    for j in range(len(leaves)):
        for i in range(3*j,3*j+3):w[i]=1<<d
        t|=1<<d
        d+=1
    assert d==(6*k+19 if strict else 3*k+4)
    size=1<<d
    full=(1<<size)-1
    patterns=[]
    for i in range(d):
        if i<3:
            unit=bytes([(0x55,0x33,0x0f)[i]])
        else:
            run=1<<(i-3)
            unit=bytes([255])*run+bytes(run)
        patterns.append(int.from_bytes(unit*(size//(8*len(unit))),"little"))
    image=1
    for a,b in zip(f,w):
        image|=xor_translate(image,a,d,patterns)|xor_translate(image,b,d,patterns)
    assert full^image==1<<t
    print('strict' if strict else 'repeated',k,d,image.bit_count(),flush=True)


for k in range(1,6):check(k,False)
check(1,True)
