"""Finite grid check for the protected OR-group bounds."""
def certify(q, a, d):
    N = q*q+q+1
    size = (N*q+99)//100-1
    k = size-(4*N-4)
    degree = q+1
    depth = (degree-1).bit_length()
    weight = degree*depth-2**depth
    h = -(-N*degree//(q*weight))
    S0 = (2*k-6+4*N//(q+2)+size//((q-3)//2)
          +2*(2*N-h*degree-1)//(q+2-h)+h)
    width = 32
    largest_batch = 8
    H=q-largest_batch-4-k//384
    prefix = [0]
    cap = 3
    for lo in range(0, k+1, width):
        hi = min(lo+width-1,k)
        for t in range(cap,largest_batch+1):
            def prefix_at(j):
                return prefix[j] if j<=lo else prefix[lo]+(j-lo)*t
            for ml in range(0,hi+1,width):
                mh = min(hi,ml+width-1)
                T = prefix_at(hi)-prefix_at(hi-mh)
                if T>=H*H:
                    break
                geom = 2*(q+2)+4*(T*(H-1)//(H*H-T))
                B = min(2*hi-ml,768)
                G = S0+hi-ml+k-3
                A = 2*N-T-geom-B
                u = S0+2*hi-ml-B
                left = (t-2)*(7*t-11)*A
                right = ((t-2)*(6*t-3)+(t+1)*(t+4))*u+(t-2)*(t+1)*(18*G+24*geom+12*B)
                if left<=right:
                    break
            else:
                break
        else:
            return ("blocked",lo)
        cap=t
        for _ in range(lo,hi+1):
            prefix.append(prefix[-1]+t)
    return cap,prefix[-1]



assert certify(407,5,6)==(6,56936)
assert certify(408,5,6)==(8,77360)
assert certify(409,5,6)==("blocked",10656)
