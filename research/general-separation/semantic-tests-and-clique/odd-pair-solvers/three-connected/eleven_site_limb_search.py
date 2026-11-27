"""Exhaust simple exterior graphs of orders 3,5,7 and all named attachments."""
from collections import Counter
from itertools import combinations
import networkx as nx
import mixed_torso_full_census as census


def graph(rows):
    g = nx.Graph()
    for i,row in enumerate(rows):
        g.add_node(i, mark=i if i < 2 else 2)
        for j in range(i):
            if row >> j & 1:
                g.add_edge(i,j)
    return g


def interiors():
    reps = []
    def collect(rows):
        if len(rows)==11:
            g=graph(rows)
            if not any(nx.is_isomorphic(g,h,node_match=lambda u,v:u['mark']==v['mark']) for _,h in reps):
                reps.append((tuple(rows),g))
        return True
    census.unique_full=collect
    census.main()
    return [rows for rows,_ in reps]


def summary(rows):
    # Interior variants capped at two per boundary, exterior incoming parity.
    n=len(rows)
    tab=[[0]*4 for _ in range(4)]
    for w in range(1<<n):
        if any(w>>i&1 and not (w&rows[i]).bit_count()%2 for i in range(2,n)):
            continue
        for s in range(4):
            if all(not (w>>i&1) or ((w&rows[i]).bit_count()+(s>>i&1))%2 for i in range(2)):
                tab[w&3][s] = min(2,tab[w&3][s]+1)
    return tab


def run():
    from edge_torso_atlas_check import witnesses
    for torso in interiors():
        physical=list(torso)
        physical[0]^=2
        physical[1]^=1
        tab=summary(physical)
        assert tab[3][2]==1
        for n in (3,5,7):
            counts=Counter()
            first=None
            for g in nx.graph_atlas_g():
                if len(g)!=n:continue
                er=[sum(1<<j for j in g[i]) for i in range(n)]
                for x,y in combinations(range(n),2):
                    for z in range(n):
                        arms=[(1<<x)|(1<<y),1<<z]
                        deg=[row.bit_count()+sum(a>>i&1 for a in arms) for i,row in enumerate(er)]
                        if any(d not in (3,5) for d in deg):
                            # A biconnected all-odd graph has no degree-one site.
                            continue
                        counts['degree_pass']+=1
                        h=g.copy()
                        h.add_edges_from([(n,n+1),(n,x),(n,y),(n+1,z)])
                        if not nx.is_biconnected(h):continue
                        counts['biconnected']+=1
                        pairs=set(combinations(range(n+2),2))
                        for w in range(1<<n):
                            drift=sum(((w&a).bit_count()%2)<<i for i,a in enumerate(arms))
                            for u in range(4):
                                ways=tab[u][drift]
                                if not ways:continue
                                total=w|(u<<n)
                                if total==(1<<(n+2))-1 and ways==1:continue
                                if any(w>>i&1 and ((er[i]&w).bit_count()+sum((u>>j&1)*(a>>i&1) for j,a in enumerate(arms)))%2==0 for i in range(n)):continue
                                pairs={pair for pair in pairs if not all(total>>i&1 for i in pair)}
                            if not pairs:break
                        if pairs:
                            rr=physical[:]+[row<<11 for row in er]
                            for i,a in enumerate(arms):
                                for j in range(n):
                                    if a>>j&1:
                                        rr[i]|=1<<(11+j)
                                        rr[11+j]|=1<<i
                            def site(i):return 11+i if i<n else i-n
                            for p,q in pairs:
                                assert witnesses(rr,site(p),site(q))
                            counts['positive']+=1
                            if first is None:first=(rr,[site(i) for i in min(pairs)])
            print('torso',torso,'order',n,counts,'positive example',first,flush=True)


if __name__=='__main__':
    run()
