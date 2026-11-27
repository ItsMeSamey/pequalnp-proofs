"""Bounded integer certificate for order 409. Each trial advances at least one whole block."""

q = 409
N = q*q+q+1
c = q+1
k = (N*q+99)//100-1-4*N+4
r = 65
reset = 768
zwidth = 256
twidth = 5000
weight = c*(c-1).bit_length()-2**((c-1).bit_length())
pins = -(-N*c//(q*weight))
S0 = (2*k-6+4*N//(q+2)+(4*N-4+k)//((q-3)//2)
      +2*(2*N-pins*c-1)//(q+2-pins)+pins)
test_cap = 2*r+2+k//reset+1
assert test_cap <= q-1
H = q-9

def box_passes(t, lo, hi, ml, Tmin, T):
    if T>=H*H:
        return False
    geom=2*(q+2)+4*(T*(H-1)//(H*H-T))
    def low(deg):
        gap=(c-deg)*N-c*T
        if gap<=0:
            return 2*N
        return q*T*(N-T)*N//(gap*gap)
    pen=4*N
    for d in range(80,361,10):
        gap=(c-d)*N-c*T
        if gap>0:
            Hdef=q*T*(N-T)//(4*gap)
            pen=min(pen,1+(2*(2*N-Tmin)+Hdef)//(d+1))
    I=2*hi-ml
    sc=4*N-2*Tmin-4+k-lo
    clean=2*(k-lo+pen-4)+2*(sc//r)
    Scap=min(S0+I,low(test_cap)+2*reset+clean)
    B=min(I,low(test_cap)+2*reset,Scap)
    u=min(Scap-B,low(2*r)+clean)
    G=min(S0+hi-ml+k-3,Scap+k-lo-3)
    p=geom+B
    lhs=(t-2)*(7*t-11)*(2*N-T-p)
    rhs=((t-2)*(6*t-3)+(t+1)*(t+4))*u+(t-2)*(t+1)*(18*G+24*p-12*B)
    return lhs>rhs

def stage_passes(t, lo, hi, prefix):
    def pf(j):
        return prefix[j] if j<=lo else prefix[lo]+(j-lo)*t
    for ml in range(0,hi+1,zwidth):
        mh=min(hi,ml+zwidth-1)
        top=pf(hi)-pf(hi-mh)
        for Tmin in range(ml,top+1,twidth):
            if not box_passes(t,lo,hi,ml,Tmin,min(Tmin+twidth-1,top)):
                return False
    return True

cap=3
prefix=[0]
for lo in range(0,k+1,zwidth):
    hi=min(lo+zwidth-1,k)
    for t in range(cap,9):
        if stage_passes(t,lo,hi,prefix):
            break
    else:
        raise AssertionError(lo)
    cap=t
    for _ in range(lo,hi+1):
        prefix.append(prefix[-1]+t)
assert (cap,prefix[-1])==(6,88022)
print(f"N={N}, k={k}, S0={S0}, cap={cap}, cumulative cap={prefix[-1]}")
