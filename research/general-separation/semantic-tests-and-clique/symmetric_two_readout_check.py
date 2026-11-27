"""Bounded graph-atlas checks of universal quadratics and two affine readouts."""
from itertools import combinations
from collections import Counter
import networkx as nx


def reduce_word(x,basis):
    while x and x.bit_length() in basis:
        x^=basis[x.bit_length()]
    return x


def basis(rows):
    pivots={}
    for row in rows:
        y=reduce_word(row,pivots)
        if y:pivots[y.bit_length()]=y
    return pivots


def witness_product(n,feasible,ref,positions):
    # Affine fibers define a simultaneous target of two arbitrary linear readouts.
    for a,b in combinations(range(1,1<<n),2):
        for u in (0,1):
            for v in (0,1):
                valid=[x for x in feasible if (a&x).bit_count()%2==u and (b&x).bit_count()%2==v]
                ls=[1<<i for i in range(n) if a>>i&1]+([0] if not u else [])
                rs=[1<<i for i in range(n) if b>>i&1]+([0] if not v else [])
                poly=0
                for l in ls:
                    for r in rs:poly^=1<<positions[l|r]
                if not valid and reduce_word(poly,ref):
                    return a,u,b,v,poly


def main():
    counter=Counter(); first=None; forest_miss=None
    for g in nx.graph_atlas_g():
        n=len(g)
        if not 1<=n<=6:continue
        N=1<<n
        cols=[0]+[1<<i for i in range(n)]+[(1<<i)|(1<<j) for i,j in combinations(range(n),2)]
        pos={m:i for i,m in enumerate(cols)}
        ev=[sum(1<<i for i,m in enumerate(cols) if m&x==m) for x in range(N)]
        adj=[sum(1<<j for j in g[i]) for i in range(n)]
        comps=[sum(1<<i for i in comp) for comp in nx.connected_components(g)]
        forest={x for x in range(N) if (not x or
                    (nx.is_forest(g.subgraph([i for i in range(n) if x>>i&1]))
                     and all((x&adj[i]).bit_count()<=2 for i in range(n) if x>>i&1)))}
        for c in range(N):
            feasible=[x for x in range(N) if all(not (x>>i&1) or
                      (x&adj[i]).bit_count()%2==(c>>i&1) for i in range(n))]
            generators=[]
            for i in range(n):
                row=(1<<pos[1<<i]) if c>>i&1 else 0
                for j in g[i]:row^=1<<pos[(1<<i)|(1<<j)]
                generators.append(row)
            for comp in comps:
                for mon in cols[:n+1]:
                    row=0
                    for i in range(n):
                        if c&comp&(1<<i):row^=1<<pos[(1<<i)|mon]
                    generators.append(row)
            refs=basis(generators)
            actual=len(cols)-len(basis(ev[x] for x in feasible))
            assert all((ev[x]&f).bit_count()%2==0 for f in refs.values() for x in feasible)
            gap=actual-len(refs)
            counter[n,gap>0]+=1
            if gap and first is None:
                ex=witness_product(n,feasible,refs,pos)
                if ex:
                    first=(n,sorted(g.edges()),c,feasible,len(refs),actual,ex,
                           [col for i,col in enumerate(cols) if ex[-1]>>i&1])
            if forest_miss is None and set(feasible)-forest:
                small=set(feasible)&forest
                for a,b in combinations(range(1,N),2):
                    def image(xs):return {((a&x).bit_count()%2,(b&x).bit_count()%2) for x in xs}
                    missing=image(feasible)-image(small)
                    if missing:
                        forest_miss=(n,sorted(g.edges()),c,feasible,sorted(small),a,b,sorted(missing))
                        break
    print('exact vs incomplete per n',sorted(counter.items()))
    print('first missing product',first)
    print('first linear-forest readout miss',forest_miss)


if __name__=='__main__':main()
