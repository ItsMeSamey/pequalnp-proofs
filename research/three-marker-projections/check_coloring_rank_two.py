from itertools import product
from check_coloring_principals import mul,power,eliminate,xor

def check(n,edges):
    d=1
    while d<n*n:d*=2
    level=d.bit_length()-2
    alpha=1<<(d//2)
    basis=[power(level,alpha,j)for j in range(n*n)]
    paired={n*u+v for u,v in edges}|{n*v+u for u,v in edges}
    c0=xor(basis[n*v+u]for u,v in edges)
    labels=[basis[n*i]for i in range(n)]+[basis[i]for i in range(n)]
    labels += [basis[n*u+v]^basis[n*v+u]for u,v in edges]
    labels += [basis[i]for i in range(n*n)if i not in paired]
    invc=power(level,c0,(1<<d)-2)
    u=[];vs=[]
    for j,label in enumerate(labels):
        u.append((0,mul(level,label,invc))if j<n or j>=2*n else (label,0))
        vs.append((1,0)if j<n else (0,1))
    h=len(labels)
    mat=[[int(i==j)^xor(mul(level,a,b)for a,b in zip(vs[i],u[j]))for j in range(h)]for i in range(h)]
    good=0
    for p in product((0,1),repeat=n):
        for q in product((0,1),repeat=n):
            proper=all((p[i]*q[j]^p[j]*q[i])==1 for i,j in edges)
            if proper:good+=1
            ad=mul(level,xor(basis[n*i]for i in range(n)if p[i]),xor(basis[j]for j in range(n)if q[j]))
            assert ad==xor(basis[n*i+j]for i in range(n)for j in range(n)if p[i]and q[j])
            if n<=2:
                for z in product((0,1),repeat=h-2*n):
                    x=p+q+z
                    c=c0^xor(v for v,t in zip(labels[2*n:],z)if t)
                    idx=[j for j,t in enumerate(x)if t]
                    assert (not eliminate(level,[[mat[i][j]for j in idx]for i in idx]))==(ad==c)
    print(n,'vertices',d,'binary field degree',h,'selectors',good,'proper assignments')

if __name__=='__main__':
    check(2,[(0,1)])
    check(3,[(0,1),(1,2),(2,0)])
    check(4,[(i,j)for i in range(4)for j in range(i)])
