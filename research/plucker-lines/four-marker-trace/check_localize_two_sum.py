"""Check localization on synthetic mode tables respecting only the pure-span axioms."""
from itertools import combinations
from random import Random

def shift(S,b):
    return {s^b for s in S}

def total(P,Q):
    return {p^q for p in P for q in Q}

rng=Random(7310865)
def subspace():
    S={0}
    for _ in range(rng.randrange(5)):
        S |= shift(S,rng.randrange(16))
    return S

def limb():
    P,Q=subspace(),subspace()
    U=total(P,Q)
    sets=[]
    for base,required in [(0,P|Q),(rng.randrange(16),P),(rng.randrange(16),Q)]:
        extras={x for x in U if rng.randrange(6)==0}
        sets.append(shift(required|extras,base))
    return P,Q,U,sets

def localized(A,B,p):
    def test00(X,Y):
        P,Q,U,sets=Y
        zero=X[3][0]
        if len(U)==1:
            return False,zero & {p}
        # A pair hit in either mode certifies a true model.
        for i,S in enumerate([P,Q],1):
            if len(S)<2:continue
            base=next(b for b in sets[i] if shift(S,b)<=sets[i])
            for x,y in combinations(S,2):
                h=x^y
                if zero & shift({x,y},p) or X[3][i] & shift({base,base^h},p):
                    return True,set()
        known=set()
        for b in U-(P|Q):
            u=next(u for u in P if b^u in Q)
            v=b^u
            base=next(k for k in sets[1] if shift(P,k)<=sets[1])
            if zero & shift({b,v},p) or X[3][1] & shift({base,base^u},p):
                if X[3][1] & shift({base,base^u},p):return True,set()
                known.add(p^b)
        assert known==zero & shift(U,p)
        return False,known
    if len(A[2])==1 or len(B[2])==1:
        return any(X & shift(Y,p) for X,Y in zip(A[3],B[3]))
    early,az=test00(A,B)
    if early:return True
    early,bz=test00(B,A)
    if early or az & shift(bz,p):return True
    assignments=[{},{}]
    for m in (1,2):
        real=[A[3][m],shift(B[3][m],p)]
        V=shift(A[2],min(real[0])) & shift(B[2],min(real[1]))
        if not V:continue
        partial=[]
        for j,(X,Y) in enumerate([(A,B),(B,A)]):
            if len(V)<=2 and len(X[2])<=4:
                partial.append((real[j]&V,True))
                continue
            hits,misses=set(),set()
            for a,b in combinations(V,2):
                h=a^b
                c=next(k for k in Y[3][0] if k^h in Y[3][0])
                assert not (X[3][0] & shift({c,c^h},p))
                hit=real[j]&{a,b}
                if hit:hits.add(min(hit))
                else:misses.update([a,b])
            if misses:
                hits=V-misses
                assert hits==real[j]&V
            partial.append((hits,bool(misses) or hits==V))
        if len(V)<=2:
            small=next(i for i in (0,1) if len([A,B][i][2])<=4)
            S=partial[small][0]
            if len(S)==2:
                if real[1-small]&S:return True  # single pair oracle
            elif S: assignments[1-small][m]=next(iter(S))
            continue
        (S,ex),(T,ey)=partial
        if S&T:return True
        if not ex and not ey: raise AssertionError('two dense tables disjoint')
        if not ex and T:assignments[0][m]=next(iter(T))
        if not ey and S:assignments[1][m]=next(iter(S))
    for j,memo in enumerate(assignments):
        if not memo:continue
        X,Y=(A,B) if j==0 else (B,A)
        for m in range(3):
            partner=(memo[m]^(p if j==0 else 0)) if m in memo else min(Y[3][m])
            assert partner in Y[3][m]
            if p^partner in X[3][m]:return True
    return False

if __name__=='__main__':
    for i in range(2500):
        A,B=limb(),limb()
        truth=set.union(*(total(x,y) for x,y in zip(A[3],B[3])))
        for p in range(16):
            assert localized(A,B,p)==(p in truth),(i,p)
    print('40,000 decisions matched direct mode sums (2,500 seeded abstract limb pairs).')
