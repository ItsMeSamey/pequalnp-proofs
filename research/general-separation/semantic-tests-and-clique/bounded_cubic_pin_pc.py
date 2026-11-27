"""Exact formal degree <=3 Boolean PC after a consistent pin-slice substitution."""
from functools import lru_cache
from itertools import combinations
from random import Random
from module_affine_escape import affine, bits, image, mask
from three_pin_quadratic_closure import truth
from one_missing_reservoir_check import host


@lru_cache(None)
def monomials(n):
    mons = [mask(group) for size in range(4) for group in combinations(range(n),size)]
    pos = {m:i for i,m in enumerate(mons)}
    low = sum(m.bit_count()<=2 for m in mons)
    maps = [[1<<pos[m|(1<<i)] for m in mons[:low]] for i in range(n)]
    return low,maps


def pc(A,pins,degree=3):
    P = mask(pins)
    free = list(bits(((1<<len(A))-1)^P))
    def pack(row):
        return mask(j for j,i in enumerate(free) if row>>i&1)
    root = affine([(pack(A[p]),(A[p]&P).bit_count()%2) for p in pins],len(free))
    if root is None:
        return True,0,0
    off,dirs = root
    n = len(dirs)
    if n>16:
        raise ValueError("bounded test max slice dimension 16")
    def embed(z):
        return mask(free[i] for i in bits(z))
    x0 = P|embed(off)
    D = list(map(embed,dirs))
    def guards(x):
        return x & image(A,x)
    c = guards(x0)
    singles = [guards(x0^d)^c for d in D]
    polycols = [c]+singles+[guards(x0^D[i]^D[j])^c^singles[i]^singles[j]
                               for i,j in combinations(range(n),2)]
    low,maps = monomials(n)
    frontier = []
    E = {}
    threshold = low if degree==3 else n+1
    def insert(row):
        while row:
            p = row.bit_length()-1
            if p not in E:
                E[p] = row
                if p<threshold:
                    frontier.append(row)
                break
            row ^= E[p]
    for i in free:
        insert(mask(j for j,v in enumerate(polycols) if v>>i&1))
    for row in frontier:
        if 0 in E:
            break
        support = list(bits(row))
        for lookup in maps:
            multiple = 0
            for j in support:
                multiple ^= lookup[j]
            insert(multiple)
    return 0 in E,len(E),n


def main():
    rng = Random(4271041)
    strong = [6372,1572,4107,1828,640,8011,161,3665,1064,4282,6570,1185,1573]
    eleven = [160,1572,10,1796,640,1859,1184,1105,1064,58,490]
    nine = [170,449,240,81,300,341,174,327,178]
    stats = {}
    def check(A,P,known=None):
        ans = truth(A,P) if known is None else known
        two,_,dim = pc(A,P,2)
        three,rank,_ = pc(A,P,3)
        assert not(ans and (two or three)) and not(two and not three)
        tag = 'YES' if ans else 'D2' if two else 'D3' if three else 'survives D3'
        stats[tag] = stats.get(tag,0)+1
        if tag=='survives D3':
            print("COUNTEREXAMPLE",A,P,dim,rank)
            return True
        return False
    for A,P in [(strong,(8,9,10)),(eleven,(8,9,10)),(nine,(0,1,2))]:
        print("fixture",len(A),pc(A,P,2),pc(A,P,3))
        check(A,P)
        for i,j in combinations(range(len(A)),2):
            B = A[:]
            B[i] ^= 1<<j
            B[j] ^= 1<<i
            if check(B,P):
                return
    for _ in range(140):
        A=strong[:]
        P=(8,9,10)
        for i in range(rng.randrange(1,5)):
            u,v=rng.sample(range(len(A)),2)
            A[u]^=1<<v
            A[v]^=1<<u
        if check(A,P):
            return
    # Fixed-reservoir expansions preserve source satisfiability.
    for A,P in [(eleven,(8,9,10)),(nine,(0,1,2)),(strong,(8,9,10))]:
        colors = [0]*len(A)
        for i,v in zip(P,(1,2,7)):
            colors[i]=v
        G=host(A,colors)
        if len(A)>13:
            continue
        print("expanded",len(A),pc(G,(0,1,2),3))
        if check(G,(0,1,2),False):
            return
    print("counts",stats)


from collections import Counter
def flat_truth(A,P):
    pm=mask(P); F=list(bits(((1<<len(A))-1)^pm))
    def pack(r):return mask(j for j,i in enumerate(F) if r>>i&1)
    flat=affine([(pack(A[p]),(A[p]&pm).bit_count()%2) for p in P],len(F))
    if flat is None:return False
    off,K=flat
    n=len(K); sz=1<<n
    allbits=(1<<sz)-1
    pats=[(allbits//((1<<(1<<j))+1))<<(1<<j) for j in range(n)]
    words=[allbits if i in P else 0 for i in range(len(A))]
    for j,i in enumerate(F):
        w=allbits if off>>j&1 else 0
        for k,v in enumerate(K):
            if v>>j&1:w ^= pats[k]
        words[i]=w
    live=allbits
    for i in F:
        y=0
        for j in bits(A[i]):y ^= words[j]
        live &= ~(y&words[i])
    return bool(live)

def probe(source, colors, trials):
    rng = Random(57112)
    pool = [host(source, colors)]
    stats = Counter()
    for trial in range(trials):
        A = rng.choice(pool)[:]
        for _ in range(rng.choice((1,1,2,3))):
            i,j = rng.sample(range(len(A)),2)
            A[i] ^= 1<<j
            A[j] ^= 1<<i
        P = (0,1,2)
        if flat_truth(A,P):
            stats["YES"] += 1
            continue
        if pc(A,P,2)[0]:
            stats["D2"] += 1
            continue
        if A not in pool:
            pool.append(A)
        if not pc(A,P,3)[0]:
            print("surviving NO",trial,A)
            return
        stats["D3"] += 1
    print("mutation walk",trials,dict(stats),"distinct retained matrices",len(pool))


if __name__ == "__main__":
    main()
    probe([170,449,240,81,300,341,174,327,178],[1,2,7]+[0]*6,1000)
    probe([6372,1572,4107,1828,640,8011,161,3665,1064,4282,6570,1185,1573],
          [0]*8+[1,2,7,0,0],2500)
