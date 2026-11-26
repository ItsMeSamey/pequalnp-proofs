"""Binary chart hitting family and an exact witness extractor."""
from itertools import combinations
from functools import reduce
from operator import xor

def remainder(a, b):
    while a.bit_length() >= b.bit_length():
        a ^= b << (a.bit_length() - b.bit_length())
    return a

def modulus(degree):
    """Trial division is polynomial in field size."""
    for p in range((1<<degree)+1,1<<(degree+1),2):
        if all(remainder(p,v) for i in range(1,degree//2+1)
               for v in range((1<<i)+1,1<<(i+1),2)):
            return p
    raise AssertionError("no irreducible polynomial")

def multiply(a,b,p):
    product=0
    while b:
        if b&1:
            product^=a
        b>>=1
        a<<=1
        if a.bit_length()==p.bit_length():
            a^=p
    return product

def seeds(m,c):
    if m==0:
        return [0]
    degree=(m<<(c+1)).bit_length()
    q=1<<degree
    p=modulus(degree)
    points=set()
    for x in range(q):
        v=1
        powers=[]
        for _ in range(m):
            powers.append(v)
            v=multiply(v,x,p)
        for tau in range(q):
            point=sum(((tau&v).bit_count()%2)<<i for i,v in enumerate(powers))
            points.add(point)
        if len(points)==1<<m:
            break
    return sorted(points)

def charts(m,c,direct=True):
    """Stream the odd XORs; the optional full-cube fallback can be faster."""
    if not m or direct and m<=10*(m<<(c+1)).bit_length():
        yield from range(1<<m)
        return
    points=seeds(m,c)
    if len(points)==1<<m:
        yield from points
        return
    for length in (1,3,5):
        for selected in combinations(points,length):
            yield reduce(xor,selected)

def add(pivots,value):
    while value:
        top=value.bit_length()-1
        if top not in pivots:
            pivots[top]=value
            return True
        value^=pivots[top]
    return False

def rank(values):
    pivots={}
    for v in values:
        add(pivots,v)
    return len(pivots)

def solve(columns,d,direct=True):
    """Input private (k), tag (b) and target-plane (h) bits in split coordinates."""
    if any(not (0<=k<1<<d and 0<=b<4 and 0<=h<4) for k,b,h in columns):
        raise ValueError("invalid input coordinates")
    if rank(k for k,b,h in columns)!=d:
        raise ValueError("compress unused private coordinates first")
    tags={}
    for k,b,h in columns:
        tags[k]=tags.get(k,0)|(1<<b)
    t=d-rank(k for k,mask in tags.items() if mask==15)
    for g in charts(2*d,2*(t+2),direct):
        a=g&((1<<d)-1)
        z=g>>d
        chosen=[]
        physical={}
        private={}
        for i,(k,b,h) in enumerate(columns):
            if b != ((k&a).bit_count()%2) + 2*((k&z).bit_count()%2):
                continue
            add(private,k)
            if add(physical,(k<<2)|h):
                chosen.append(i)
        if len(physical)-len(private)==2:
            return chosen
    return None
