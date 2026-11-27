"""Return an independent generating list of affine guard sums on the physical pin slice."""
from itertools import combinations
from random import Random
from module_affine_escape import affine, bits, image, mask
from three_pin_template_solver import basis_of, kernel
from three_pin_quadratic_closure import closures, truth


def certificate(A,pins,all_cuts=False):
    n = len(A)
    P = mask(pins)
    free = list(bits(((1<<n)-1)^P))
    pin_rows = [(mask(j for j,v in enumerate(free) if A[p]>>v&1),
                 (A[p]&P).bit_count()%2) for p in pins]
    rank = len(basis_of(v for v,_ in pin_rows))
    solution = affine(pin_rows,len(free))
    if solution is None:
        return {"inconsistent_pins":True}
    x,K = solution
    def embed(v):
        return mask(free[j] for j in bits(v))
    origin = P | embed(x)
    directions = list(map(embed,K))
    def guards(w):
        return w & image(A,w) & ~P
    c = guards(origin)
    singles = [guards(origin^v)^c for v in directions]
    pairs = [guards(origin^u^v)^c^singles[i]^singles[j]
             for (i,u),(j,v) in combinations(enumerate(directions),2)]
    packed = [sum(((row>>i)&1)<<j for j,row in enumerate([c]+singles+pairs)) for i in free]
    def coeff(L):
        p = 0
        for i in bits(L):
            p ^= packed[i]
        return p
    f = len(free)
    linear = kernel([mask(i for i,p in enumerate(packed) if p>>j&1)
                     for j in range(1+len(K),1+len(K)+len(pairs))],f)
    def physical_ranks(L):
        left = embed(L)
        right = ((1<<n)-1)^P^left
        return tuple(len(basis_of(A[i]&~S for i in bits(S))) for S in (left,right))
    for l in linear:
        assert coeff(l).bit_length() <= 1+len(K)
        assert max(physical_ranks(l)) <= rank
    # Solve for a sum equal to one in the span of all affine sums.
    affine_rows = [(mask(i for i,l in enumerate(linear) if coeff(l)>>j&1),int(j==0))
                   for j in range(1+len(K))]
    unit = affine(affine_rows,len(linear))
    shore = None
    if unit is not None:
        l = 0
        for j in bits(unit[0]):
            l ^= linear[j]
        shore = embed(l),physical_ranks(l)
        assert coeff(l)==1 and max(shore[1]) < rank and l not in (0,(1<<f)-1)
    low = 0
    if all_cuts:
        for l in range(1,(1<<f)-1):
            ranks = physical_ranks(l)
            low += max(ranks)<=rank
            p = coeff(l)
            if p.bit_length()<=1+len(K):
                assert max(ranks)<=rank
            if p==1:
                assert max(ranks)<rank
    return dict(rank=rank,affine_image_rank=len(basis_of(coeff(l) for l in linear)),
                affine_sums=[(embed(l),coeff(l)) for l in linear],contradiction=shore,
                paired_low_cuts=low if all_cuts else None)


def main():
    rng = Random(491)
    def report(name,A,P):
        s = certificate(A,P,len(A)-3<=10)
        bounds = closures(A,P)
        print(name, "affine-image rank",s["affine_image_rank"],"constant shore",s["contradiction"],
              "static/iterative",bounds,"paired cuts <=k",s["paired_low_cuts"])
        return s
    for yes in (False,True):
        m = 6
        A = [0]*(3+2*m)
        def edge(i,j):
            A[i] |= 1<<j
            A[j] |= 1<<i
        edge(*( (0,1) if yes else (1,2) ))
        for i in range(m):
            edge(1,3+i)
            edge(2,3+m+i)
            if i<m//2:
                edge(0,3+i)
                edge(0,3+m+i)
                for j in range(m):
                    edge(3+i,3+m+j)
            for j in range(i):
                for start in (3,3+m):
                    if rng.randrange(2):
                        edge(start+i,start+j)
        report("prime-shore "+str(yes),A,(0,1,2))
    report("nine-site NO",[170,449,240,81,300,341,174,327,178],(0,1,2))
    for n in (8,10,14,20,30):
        A = [((1<<n)-1)^mask({i,(i-1)%n,(i+1)%n}) for i in range(n)]
        report("even co-cycle "+str(n),A,(0,1,2))
    A = [160,1572,10,1796,640,1859,1184,1105,1064,58,490]
    P = (8,9,10)
    report("known immune NO",A,P)
    hits = []
    for i,j in combinations(range(11),2):
        B = A[:]
        B[i] ^= 1<<j
        B[j] ^= 1<<i
        if not truth(B,P) and not closures(B,P)[1]:
            out = certificate(B,P,True)
            hits.append((i,j,out["affine_image_rank"],out["paired_low_cuts"]))
    print("immune single-edge perturbations",hits)
    assert hits
    strong = [6372,1572,4107,1828,640,8011,161,3665,1064,4282,6570,1185,1573]
    assert not truth(strong,P) and closures(strong,P)==(False,False)
    strong_result = report("strong rank-only immune NO",strong,P)
    assert strong_result["rank"] == 3 and strong_result["paired_low_cuts"] == 0
    free_mask = ((1 << len(strong))-1) ^ mask(P)
    ok_pins = sum((lambda w: not image(strong,w)&mask(P))(mask(P)|s)
                  for s in range(1 << len(strong)) if not s & ~free_mask)
    assert ok_pins == 128
    from collections import Counter
    histogram = Counter()
    for l in range(1,1 << len(strong)):
        if l & ~free_mask or l==free_mask:
            continue
        ranks = [len(basis_of(strong[i]&~u for i in bits(u))) for u in (l,l^free_mask)]
        histogram[max(ranks)] += 1
    print("strong fixture cut maximum histogram",sorted(histogram.items()),"pin-slice points",ok_pins)


if __name__=="__main__":
    main()
