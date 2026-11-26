"""Independent GF(2) checks of rectangle quotients and projected-component sums."""
from itertools import product
from random import Random

def span(cols):
    S={0}
    for c in cols:S|={x^c for x in S}
    return frozenset(S)

def parity(a,b):return (a&b).bit_count()%2

def subspaces(n):
    todo=[frozenset({0})];seen=set(todo)
    for S in todo:
        for v in range(1<<n):
            U=S|{v^x for x in S}
            if U not in seen:seen.add(U);todo.append(U)
    return todo

def traces(cols, forms, T, p):
    return {x for d in forms if all(parity(d^p,t)==0 for t in T)
            for x in span([c for c in cols if not parity(d,c)]) if x in T}

def instance(rng,h,c):
    # W has the low h coordinates; its first c coordinates belong to T.
    W=frozenset(range(1<<h));tb=[1<<j for j in list(range(c))+list(range(h,h+4-c))]
    T=span(tb);ra=h+4-c;rb=h+1
    A=[rng.randrange(1<<ra) for i in range(rng.randrange(1,ra+2))]
    # Ensure span(A,T) actually contains W, with a random basis.
    A+=[(1<<j)^rng.choice(sorted(T)) for j in range(c,h)]
    B=[1<<j for j in range(rb)]
    for i in range(2*rb):
        v,w=rng.sample(range(rb),2) if rb>=2 else (0,0)
        if v!=w:B[v]^=B[w]
    B.extend(rng.randrange(1<<rb) for _ in range(rng.randrange(4)))
    lam=rng.randrange(1<<ra);p=rng.choice([v for v in T if not parity(lam,v)])
    mask=(1<<h)-1
    L={(w,d&mask) for d in range(1<<rb) for w in span(x for x in B if not parity(d,x)) if w in W}
    outside={(x^p,d&mask) for d in range(1<<ra) if all(not parity(d^lam,t) for t in tb)
             for x in span(v for v in A if not parity(d,v)) if (x^p) in W}
    spaces=subspaces(h);candidates=[]
    for J in spaces:
        for H in spaces:
            if not H<=J:continue
            for a in J:
                if a!=min(a^z for z in H):continue
                flux={a^z for z in H}
                covectors={tuple(parity(d,j) for j in sorted(J)):d for d in W}
                for eta in covectors.values():
                    if any(parity(eta,v) for v in flux):continue
                    box={(v,d) for v in flux for d in W if all(not parity(d^eta,j) for j in J)}
                    if not box<=L:continue
                    if any(parity(eta^lam,j) for j in J&T):continue
                    candidates.append((a,H,J,eta,box))
    # Sample full contractions and test independently in their quotient coordinates.
    for a,H,J,eta,box in rng.sample(candidates,min(10,len(candidates))):
        R=span(T|J)
        rep=lambda v:min(v^h for h in H)
        quotient_forms=[d for d in range(1<<ra) if all(not parity(d,h) for h in H)]
        query=any(all(not parity(d^lam,t) for t in tb)
                  and all(not parity(d^eta,j) for j in J)
                  and rep(p^a) in span(rep(v) for v in A if not parity(d,rep(v)))
                  for d in quotient_forms)
        assert query==bool(outside&box)
        assert len({rep(v) for v in R})==len(R)//len(H)
    cheap=[box for a,H,J,eta,box in candidates if len(span(T|J))//len(H)<=8]
    covered=set().union(*cheap)
    relevant={cell for cell in L if all(not parity(cell[1]^lam,t) for t in W&T)}
    if relevant<=covered: assert bool(L&outside)==bool(covered&outside)
    return len(candidates)

def component_trial(rng):
    n=rng.randrange(2,5);T=frozenset(range(16));lam=rng.randrange(1,16)
    K={t for t in T if not parity(lam,t)};allcols=[];tables=[];answers=[]
    for i in range(n):
        # Private projected axes are independent, with arbitrary T tails.
        C=[(1<<(4+i))^rng.randrange(16) for _ in range(rng.randrange(1,5))]
        if rng.randrange(2):C.append(rng.randrange(16))
        local=traces(C,[lam,lam^(1<<(4+i))],T,lam);tables.append(local);allcols+=C
        visited={};missing=set()
        for a in sorted(K):
            for b in sorted(K):
                if b<=a:continue
                v=a^b;rep=lambda x:min(x,x^v)
                hit=any(rep(a) in span(rep(c) for c in C if not parity(d,rep(c))) for d in [lam,lam^(1<<(4+i))])
                assert hit==bool(local&{a,b})
                if not hit:missing.update((a,b))
        if missing:
            assert K-missing==local;answers.append(local)
        else:
            assert len(local)>=len(K)-1;answers.append(None)
    full=traces(allcols,[lam^(i<<4) for i in range(1<<n)],T,lam)
    bits={0}
    for B in tables:bits={a^b for a in bits for b in B}
    assert bits==full
    if None in answers and sum(x is None or len(x)>1 for x in answers)>=2:assert full==K

if __name__=="__main__":
    rng=Random(852);boxes=0
    for h in range(4):
        for c in range(h+1):
            for _ in range(16):boxes+=instance(rng,h,c)
    for _ in range(200):component_trial(rng)
    print(f"160 random cuts ({boxes} consistent rectangles) and 200 component tests passed")
