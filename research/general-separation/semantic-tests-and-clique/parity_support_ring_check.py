"""Finite parity-cell tests over GF(16)[F2^h], with packed scalar coefficients."""
from functools import reduce
from operator import xor
from random import Random
from quaternary_support_check import times, inverse, determinant, minors, base, omega


class Ring:
    def __init__(self,h):
        self.size=1<<h

    def coeff(self,x,i):
        return x>>(4*i)&15

    def aug(self,x):
        return reduce(xor,(self.coeff(x,i) for i in range(self.size)),0)

    def mul(self,x,y):
        out=0
        for i in range(self.size):
            for j in range(self.size):
                out^=times[self.coeff(x,i)][self.coeff(y,j)]<<(4*(i^j))
        return out

    def scale(self,x,c):
        return sum(times[self.coeff(x,i)][c]<<(4*i) for i in range(self.size))

    def inv(self,x):
        a=self.aug(x)
        return self.scale(x,inverse[times[a][a]]) if a else None


def pivot_eval(mat,ring,t):
    a=[row.copy() for row in mat]
    n=len(a)
    for i in range(0,n,2):
        a[i][i+1]^=t
    ans=1
    for i in range(0,n,2):
        pivot=a[i][i+1]
        inv=ring.inv(pivot)
        if inv is None:return None
        ans=ring.mul(ans,pivot)
        for k in range(i+2,n):
            for l in range(k+1,n):
                cross=ring.mul(a[i][k],a[i+1][l])^ring.mul(a[i][l],a[i+1][k])
                a[k][l]^=ring.mul(inv,cross)
    return ans


def pf_interpolate(mat,ring):
    needed=len(mat)//2+1
    pts=[]
    for t in range(16):
        value=pivot_eval(mat,ring,t)
        if value is not None:
            pts.append((t,value))
            if len(pts)==needed:break
    assert len(pts)==needed
    out=0
    for x,y in pts:
        c=1
        for t,_ in pts:
            if t!=x:c=times[c][times[t][inverse[t^x]]]
        out^=ring.scale(y,c)
    return out


def parity_eval(J,columns,z,h):
    n=len(J)
    ring=Ring(h)
    X=[v<<(4*b) for v,b in zip(z,columns)]
    full=0
    for odd in (0,1):
        m=n+odd
        mat=[[0]*(2*m) for _ in range(2*m)]
        weights=X+[1]*odd
        for i in range(m):
            if i<n:mat[i][m+i]=1
            for j in range(i+1,m):
                b=J[i][i] if j==n else times[J[i][j]][J[i][j]]^times[J[i][i]][J[j][j]]
                mat[i][j]=b
                mat[m+i][m+j]=ring.scale(ring.mul(weights[i],weights[j]),times[b][b])
        full^=pf_interpolate(mat,ring)
    expected=0
    for s,det in enumerate(minors(J)):
        if det:
            b=0
            w=1
            for j in range(n):
                if s>>j&1:
                    b^=columns[j]
                    w=times[w][z[j]]
            expected^=w<<(4*b)
    assert full==expected


def host(m):
    classes=[0]*m+[1]*m+[2,3]
    n=len(classes)
    u,w=n-2,n-1
    old=[[int((i==j and classes[i]==0) or (i!=j and
          (u in (i,j) or classes[i]==classes[j]==1))) for j in range(n)] for i in range(n)]
    for i in (u,w):
        for j in (u,w):old[i][j]^=omega
    new=[[x^int(classes[i] in (0,2) and classes[j] in (0,2))
          for j,x in enumerate(row)] for i,row in enumerate(old)]
    cells=[]
    for J in (old,new):
        C=[[J[classes.index(a)][classes.index(b)]^(a==b) for b in range(4)] for a in range(4)]
        expected=[]
        for parity in range(16):
            reduced=[[int(i==j)^(C[i][j] if parity>>j&1 else 0) for j in range(4)] for i in range(4)]
            expected.append(determinant(reduced))
        for s,d in enumerate(minors(J)):
            p=reduce(xor,(1<<c for j,c in enumerate(classes) if s>>j&1),0)
            assert expected[p]==d
        cells.append(expected)
    assert not any(b and not a for a,b in zip(*cells))
    assert any(a and not b for a,b in zip(*cells))


if __name__=='__main__':
    rng=Random(7285)
    for h in range(3):
        R=Ring(h)
        for _ in range(120):
            u=rng.getrandbits(4*R.size); a=R.aug(u)
            assert R.mul(u,u)==times[a][a]
            if a:assert R.mul(u,R.inv(u))==1
            else:assert R.inv(u) is None
    R=Ring(1)
    eps=1^16  # nilpotent nonzero, forcing the first interpolation point to fail
    assert eps!=0 and R.mul(eps,eps)==0
    assert pivot_eval([[0,eps],[eps,0]],R,0) is None
    assert pf_interpolate([[0,eps],[eps,0]],R)==eps
    for n in range(4):
        for _ in range(20):
            J=[[0]*n for i in range(n)]
            for i in range(n):
                for j in range(i,n):J[i][j]=J[j][i]=rng.choice(base)
            parity_eval(J,[rng.randrange(4) for j in range(n)],[rng.randrange(16) for j in range(n)],2)
    host(2)
    host(3)
    print('360 ring elements, explicit nilpotent pivot, 80 interpolation tests, all 16 cells of both hosts passed')
