"""Find s such that the supplied binary-linear A plus multiplication by s is invertible."""
from field_plane_root import rational_roots
from quadratic_image import bits
from quadratic_target import insert
from star_drift_witness import _solve_square


def _coefficients(field,coeffs):
    coeffs=tuple(coeffs)
    if len(coeffs)>field.m or any(type(a) is not int or not 0<=a<field.size for a in coeffs):
        raise ValueError("expected at most m packed linearized coefficients")
    return coeffs+(0,)*(field.m-len(coeffs))


def _columns(field,coeffs):
    cols=[]
    for i in range(field.m):
        z=1<<i
        total=0
        for a in coeffs:
            total ^= field.mul(a,z)
            z=field.mul(z,z)
        cols.append(total)
    return cols


def _safe(field,cols,s):
    pivots={}
    return all(insert(v^field.mul(s,1<<i),0,pivots) for i,v in enumerate(cols))


def moment(field,coeffs,t):
    """Power sum over all safe slopes, in K; zero to the zeroth power counts as one."""
    coeffs=_coefficients(field,coeffs)
    if type(t) is not int or t<0:
        raise ValueError("invalid exponent")
    if not t: return 1
    m,N=field.m,field.size-1
    t=1+(t-1)%N
    target=t%N
    marks=list(bits(t))
    full=(1<<len(marks))-1
    # Row k gives the contribution for assigning marked bit k to destination d.
    weights=[]
    for k in marks:
        powers=list(coeffs)
        for _ in range(k): powers=[field.mul(a,a) for a in powers]
        weights.append([powers[(d-k)%m] for d in range(m)])
    per_dest=[]
    for d in range(m):
        products=[1]*(full+1)
        for subset in range(1,full+1):
            lo=subset & -subset
            products[subset]=field.mul(products[subset^lo],weights[lo.bit_length()-1][d])
        per_dest.append(products)
    total=int(not target)  # sum over the full field, t>0
    for start in range(len(marks)+1):
        states={(full,start):1}
        for d,products in enumerate(per_dest):
            nxt={}
            desired=(target>>d)&1
            for (unused,carry),weight in states.items():
                subset=unused
                while True:
                    v=carry+subset.bit_count()-desired
                    if v>=0 and not(v&1) and products[subset]:
                        key=(unused^subset,v//2)
                        nxt[key]=nxt.get(key,0)^field.mul(weight,products[subset])
                    if not subset: break
                    subset=(subset-1)&unused
            states={key:v for key,v in nxt.items() if v}
        total ^= states.get((0,start),0)
    return total


def find(field,coeffs):
    """Return one verified safe slope in time polynomial in m and their number g."""
    coeffs=_coefficients(field,coeffs)
    cols=_columns(field,coeffs)
    moments=[]
    bound=1
    while 2*bound-1 < field.size-1:
        while len(moments)<2*bound:
            moments.append(moment(field,coeffs,len(moments)))
        # For bound >= g, the largest nonsingular leading Hankel matrix has size g.
        for r in range(bound,0,-1):
            h=[moments[i:i+r] for i in range(r)]
            locator=_solve_square(field,h,moments[r:2*r])
            if locator is not None:
                for s in rational_roots(field,tuple(locator)+(1,)):
                    if _safe(field,cols,s):
                        return s
                break
        bound*=2
    for s in range(field.size):
        if _safe(field,cols,s):
            return s
    raise ArithmeticError("safe slope parity violated")
