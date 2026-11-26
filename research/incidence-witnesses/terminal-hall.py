from fractions import Fraction as F
N,k,q,L=161203,402,401,646425
for Q,steps in ((0,66),(5928,61),(24080,46)):
    z=count=0
    while (m:=N-k*z-Q)>0:
        m0=m+Q
        B=(m0*m0-F(21,k)*m0*(N-m0))/N-Q
        edges=0
        for d in range(1,q-z+1):
            i=d-1
            g=k-F(2*N*i,m)
            deficit=min(m,N*(i+21)//423)
            if g>0 and g*g>q:
                deficit=min(deficit,int(q*N*(N-m)/(g*g*m+q*(N-m))))
            edges+=m-deficit
            if d>=2 and max((d+1)*B,F(d+1,d)*edges)>L:
                break
        else:
            break
        count+=1
        z+=d-1
    assert count==steps,(Q,count)
    print(Q,count,z)
