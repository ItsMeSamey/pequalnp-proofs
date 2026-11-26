for q in range(289,377):
    n=q*q+q+1
    d=q*q-20*q
    def g(x):
        return q*x//(q*q-x)
    assert n-d>g(d)+1
    u=(q*d+2*(q-1)*(n-d))//((q-1)**2-d)
    h0=d-u
    assert 0<=h0<=d and q**3<=(q*q-d)**2
    s=2*n+2*d-1-u-g(d)-g(h0)
    assert 100*s>=n*q
    print(q,s,(n*q+99)//100)
