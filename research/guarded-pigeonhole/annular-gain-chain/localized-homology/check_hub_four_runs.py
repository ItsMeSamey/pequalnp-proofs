from itertools import product,combinations,permutations

def direct(w,p,q):
    n=len(w);a=(p+1)%n
    if w[a]==w[q]:return a!=q
    return any(w[i]==w[a] and w[(i+1)%n]==w[q] and i!=a and (i+1)%n!=q for i in range(n))

def hard(w,p,q):
    n=len(w)
    # Start at crossing i, then move clockwise or counterclockwise;
    # the immediately adjacent internal passage belongs to a two-leaf run,
    # and the run on the other side is singleton.
    for i,j in ((p,q),(q,p)):
        if w[i]==w[(i+1)%n]:continue
        if j==(i+1)%n and w[(i+1)%n]==w[(i+2)%n]!=w[(i+3)%n] and w[(i-1)%n]!=w[i]:return True
        if j==(i-1)%n and w[i]==w[(i-1)%n]!=w[(i-2)%n] and w[(i+1)%n]!=w[(i+2)%n]:return True
    return False

def joined(perm,a,b):
    x=a
    while True:
        if x==b:return True
        x=perm[x]
        if x==a:return False

def main():
    cases=exceptional=0
    for a,b,c,d in product(range(1,6),repeat=4):
        w='X'*a+'Y'*b+'X'*c+'Y'*d
        for p,q in combinations(range(len(w)),2):
            exc=hard(w,p,q)
            assert exc==(not direct(w,p,q) and not direct(w,q,p))
            cases+=1;exceptional+=exc
    transfers=0
    # X's two marked leaves are a=0,b=1; then Y-long, X-long, Y-single.
    for t,l in product(range(1,4),repeat=2):
        n=t+l+3
        X=[0,1]+list(range(2+l,n-1)); Y=list(range(2,2+l))+[n-1]
        for xp in permutations(X):
            Tx=dict(zip(X,xp))
            for yp in permutations(Y):
                Ty=dict(zip(Y,yp));T={**Tx,**Ty}
                native={i:(v+1)%n for i,v in T.items()}
                exits={n-1,1+l}
                def exit_leaf(leaf):
                    while Ty[leaf] not in exits:leaf=Ty[leaf]+1
                    return Ty[leaf]
                same=exit_leaf(n-1)==n-1
                ci=[X] if same else [[0,1],X[2:]]
                cap={z:group[(i+1)%len(group)] for group in ci for i,z in enumerate(group)}
                assert joined(native,0,1)==joined({x:cap[Tx[x]] for x in X},0,1)
                transfers+=1
    print(cases,'four-run mark pairs;',exceptional,'exceptional;',transfers,'full transfer comparisons')
if __name__=='__main__':main()
