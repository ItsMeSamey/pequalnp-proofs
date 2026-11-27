"""Polynomial recognition of b*x+c*x^(2^j) plus a binary rank-k error."""
from field_rank_drift import field_solve, frob_powers
from quadratic_centroid import independent


def _unpower(f,x,r):
    return frob_powers(f,x,(-r)%f.m)[-1]


def _decode(f,cols,width,k):
    # W is monic of q-degree k, P has q-degree at most width+k.
    def equations():
        for i,y in enumerate(cols):
            ys=frob_powers(f,y,k)
            yield ys[:-1]+frob_powers(f,1<<i,width+k),ys[-1]
    sol=field_solve(f,equations(),width+2*k+1)
    if sol is None:return None
    W=sol[:k]+[1]
    remainder=sol[k:]
    quotient=[0]*(width+1)
    for j in range(width,-1,-1):
        x=_unpower(f,remainder[j+k],k)
        quotient[j]=x
        for l,power in enumerate(frob_powers(f,x,k)):
            remainder[j+l]^=f.mul(W[l],power)
    if any(remainder) or any(quotient[1:-1]):return None
    return quotient[0],quotient[-1]


def fits(f,columns,k,*,include_scalar=False):
    """Yield checked (b,c,j) for each admissible 1<=j<d; scalar repeated if enabled."""
    cols=tuple(columns)
    if len(cols)!=f.m or any(type(x)!=int or not 0<=x<f.size for x in cols):
        raise ValueError("invalid raw columns")
    if type(k)!=int or k<0:raise ValueError("invalid rank")
    for j in range(1,f.m):
        width=min(j,f.m-j)
        if width+2*k>=f.m:continue
        rotation=0 if j==width else width
        rotated=[frob_powers(f,y,rotation)[-1] for y in cols] if rotation else cols
        fit=_decode(f,rotated,width,k)
        if fit is None:continue
        b,c=fit
        if rotation:
            b,c=_unpower(f,c,rotation),_unpower(f,b,rotation)
        if not c and not include_scalar:continue
        residual=[]
        for i,y in enumerate(cols):
            x=1<<i
            sigma=frob_powers(f,x,j)[-1]
            residual.append(y^f.mul(b,x)^f.mul(c,sigma))
        if len(independent(residual))<=k:yield b,c,j
