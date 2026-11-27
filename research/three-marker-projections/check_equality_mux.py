from itertools import product

def check(x,q,a,b):
    ident=(0,1,2,3)
    gates=[
        (1,2,0,3) if x else ident,
        (0,1,3,4,2) if a else (*ident,4),
        (0,3,2,4,1) if b else (*ident,4),
        (2,0,1,3) if q else ident,
        (2,1,0,3)]
    p={}
    for h,g in enumerate(gates):
        for i,j in enumerate(g):
            p[h,i]=(h,j) if j==4 else ((h+1)%len(gates),j)
    s=(0,3);t=(1,0);v=p[s]
    while v not in (s,t):v=p[v]
    return v==t

if __name__=='__main__':
    for a,b in product((0,1),repeat=2):
        row=[int(check(x,q,a,b)) for x,q in product((0,1),repeat=2)]
        assert row==[a,0,0,b]
        print(a,b,row)
