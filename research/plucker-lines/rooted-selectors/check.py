def rank(xs):
    b={}
    for x in xs:
        while x and x.bit_length() in b:
            x ^= b[x.bit_length()]
        if x:
            b[x.bit_length()]=x
    return len(b)

def words():
    v=list(range(1,8))
    sums=[0]
    for e in v:
        sums += [a^e for a in sums]
    result=[]
    for c,syndrome in enumerate(sums):
        if syndrome or c&3!=2:
            continue
        for w in range(8):
            d=sum(((w&e).bit_count()%2)<<i for i,e in enumerate(v))
            if d&1 and not(c&d):
                result.append((c,d))
    return result

P=[2,5,10,4]
Q=[12,12,3,3]
for s in range(16):
    rest=15^s
    assert rank(P[i]&rest for i in range(4) if s>>i&1)==rank(Q[i]&rest for i in range(4) if s>>i&1)
def pinned(A):
    return [s for s in range(16) if s&6==6 and all(not(s>>i&1 and (s&a).bit_count()%2) for i,a in enumerate(A))]
assert pinned(P)==[] and pinned(Q)==[15]
assert words()==[(42,85),(82,45)]
assert all(((c>>3)^(d>>4))&1==0 for c,d in words())
print('Fano masks, 16 paired parity checks, and rooted fibers verified')
