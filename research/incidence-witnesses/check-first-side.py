for q in range(289,337):
    n=q*q+q+1
    d=q*q-24*q
    bad=q*d//(q*q-d)
    assert n-d>bad+1
    u=(q*d+2*(q-1)*(n-d))//((q-1)**2-d)
    s=2*n+d-1-bad+(n-u+1)//2
    assert 100*s>=n*q
    print(q,s,(n*q+99)//100)
