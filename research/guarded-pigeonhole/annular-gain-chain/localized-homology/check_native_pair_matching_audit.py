"""Enumerate real patch tables, packings, and physical refinements on small hosts."""
from itertools import combinations,combinations_with_replacement,permutations
from random import Random
import networkx as nx


def passes(rows):
    options=[set(column) for column in zip(*rows)]
    def check(prefix,used,available):
        for i in available:
            for o in options[i]-used:
                if any(o in options[j] for j,_ in prefix):continue
                seq=prefix+[(i,o)]
                if not any(all(row[j]==v for j,v in seq) for row in rows):return False
                if not check(seq,used|{o},available-{i}):return False
        return True
    return check([],set(),set(range(len(options))))


def audit(sigma,pairs,totals):
    n=len(sigma);g=n//3;G=range(g)
    def step(v,m):return sigma[3*(v//3)+(v%3+(m>>(v//3)&1))%3]
    def joined(a,b,m):
        x=a
        while True:
            if x==b:return True
            x=step(x,m)
            if x==a:return False
    pred=[sigma.index(i)//3 for i in range(n)]
    cards={}
    for z in [*combinations(G,1),*combinations(G,2)]:
        internal={v for v in range(n) if v//3 in z and pred[v] in z}
        ins=[v for v in range(n) if v//3 in z and pred[v] not in z]
        rows={}
        for sub in range(1<<len(z)):
            mask=sum((sub>>j&1)<<v for j,v in enumerate(z));out=[]
            for v in ins:
                while v//3 in z:v=step(v,mask)
                out.append(v)
            rows[tuple(out)]=mask
        cards[z]=(not ins or passes(rows),internal,ins,rows)
    for a,b in pairs:
        def eligible(z):
            ok,I,_,_=cards[z]
            return ok and not {a,b}&I
        cost={v:int(not eligible((v,))) for v in G}
        graph=nx.Graph()
        graph.add_nodes_from(G)
        graph.add_weighted_edges_from((i,j,cost[i]+cost[j]) for i,j in combinations(G,2) if eligible((i,j)))
        matching=[tuple(sorted(e)) for e in nx.max_weight_matching(graph)]
        free=set(G)-set(v for e in matching for v in e)
        extra={v for v in free if cost[v]}
        def brute(pool):
            if not pool:return 0
            v=min(pool);rest=pool-{v}
            return min([cost[v]+brute(rest)]+[brute(rest-{w}) for w in rest if graph.has_edge(v,w)])
        if brute(set(G))!=len(extra):raise AssertionError('packing')
        patches=matching+[(i,) for i in free-extra]
        for sub in range(1<<len(extra)):
            m=sum((sub>>j&1)<<v for j,v in enumerate(sorted(extra)))
            D=nx.DiGraph();D.add_nodes_from([a,b])
            for v in range(n):
                if v//3 in extra:D.add_edge(v,step(v,m))
            for z in patches:
                _,_,ins,rows=cards[z]
                for row in rows:D.add_edges_from(zip(ins,row))
            ok=nx.has_path(D,a,b)
            truth=any(joined(a,b,t) for t in range(1<<g) if all(t>>x&1==m>>x&1 for x in extra))
            if ok!=truth:raise AssertionError('decision')
            if ok:
                path=nx.shortest_path(D,a,b)
                for z in patches:
                    _,_,ins,rows=cards[z]
                    turns=[(ins.index(i),o) for i,o in zip(path,path[1:]) if i in ins]
                    m|=next(mask for row,mask in rows.items() if all(row[i]==o for i,o in turns))
                if not joined(a,b,m):raise AssertionError('witness')
            totals[1+int(ok)]+=1
        totals[0]+=1


if __name__=='__main__':
    r=Random(7571);totals=[0,0,0]
    for g,ct in [(2,24),(3,24),(4,18),(5,12)]:
        for _ in range(ct):
            allpairs=list(combinations_with_replacement(range(3*g),2))
            audit(r.sample(range(3*g),3*g),r.sample(allpairs,12),totals)
    print(totals,'root queries, negative branches, witnessed positive branches')
