from math import exp,log1p,ceil,floor

def av(n,size,k):
    return exp(sum(log1p(-size/(n-j)) for j in range(k)))

def bound(q,k,m,dev_u,dev_l,dev_a):
    n=q*q+q+1;c=q+1
    f=av(n,c,k); f2=av(n,2*c-1,k)
    def var(d): return max(0,d*f*(1-f)+d*(d-1)*(f2-f*f))
    pl=ceil(f*c+dev_l);pa=floor(f*m-dev_a)
    lo=floor(f*n-dev_u);hi=ceil(f*n+dev_u)
    bad=var(n)/dev_u**2+var(c)/(var(c)+dev_l**2)+var(m)/(var(m)+dev_a**2)
    a=max(0,f-av(n,c+m,k)-bad)
    b=av(lo,pl,k)*(1-av(hi,pa,k))
    count=n*(c-k)-2*n*(q-1)/(q-m)
    return count*a*b/(n*q)

if __name__=='__main__':
    q=401
    best=(0,None)
    for k in [130,150,160,175,185,195,205]:
        for m in [335,350,360,370,380]:
            for dl in [40,50,60,70,80]:
                for da in [40,50,60,70,80]:
                    pars=(k,m,1000,dl,da)
                    val=bound(q,*pars)
                    if val>best[0]:best=(val,pars)
    print(best)
