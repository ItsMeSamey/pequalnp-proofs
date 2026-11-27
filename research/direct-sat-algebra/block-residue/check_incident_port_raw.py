"""04-only independent raw original edge and perfect-matching enumeration."""
from itertools import product
from incident_port import PortGadget, block_gadgets


def span(rows):
    out={0}
    for r in rows:
        out |= {w^r for w in out}
    return out


def coords(mask,chords):
    return sum(((mask>>j)&1)<<i for i,j in enumerate(chords))


def matchings(n, edges):
    adj=[[] for _ in range(n)]
    for j,(u,v) in enumerate(edges):
        assert u!=v
        adj[u].append((v,j)); adj[v].append((u,j))
    assert len({tuple(sorted(e)) for e in edges})==len(edges)
    def visit(left,mask):
        if not left:
            yield mask
            return
        bit=left & -left
        for v,j in adj[bit.bit_length()-1]:
            if left>>v&1:
                yield from visit(left^bit^(1<<v),mask|(1<<j))
    return visit((1<<n)-1,0)


def check(n,edges,pairs):
    g=PortGadget(n,edges,pairs)
    chords=tuple(g.chords)
    loops={e for e,(u,v) in enumerate(edges) if u==v}
    assert loops==set(g.loops) and loops<=set(chords)
    assert set(g.outer)==set(range(len(edges)))-loops
    even={}; compatible=[]; unions=set()
    for s in range(1<<len(edges)):
        degree=[0]*n
        for e,(u,v) in enumerate(edges):
            if s>>e&1:
                degree[u]+=1; degree[v]+=1
        if any(d%2 for d in degree):continue
        y=coords(s,chords)
        assert y not in even
        even[y]=s
        if any((s>>i)&(s>>j)&1 for i,j in pairs):continue
        compatible.append(y)
        if all(not(s>>e&1) for e in loops) and all(d<=2 for d in degree):
            unions.add(s)
    assert len(even)==1<<len(chords)
    actual=set(matchings(g.vertices,g.edges))
    projections=set()
    for w in actual:
        s=sum(((w>>j)&1)<<e for e,j in g.outer.items())
        assert g.project(w)==coords(s,chords)
        projections.add(s)
    assert projections==unions
    for s in unions:
        w=g.lift([e for e in range(len(edges)) if s>>e&1])
        assert w in actual and all(((s>>e)^(w>>j))&1==0 for e,j in g.outer.items())
    annihilators=span([coords(s,chords) for s in projections]+[coords(1<<e,chords) for e in loops])
    assert annihilators==span(compatible)
    # Input basis rows of a matching hull need not themselves be matchings.
    for j in range(len(g.edges)):
        read=sum(1<<i for i,e in enumerate(chords) if g.outer.get(e)==j)
        assert g.project(1<<j)==read
    pieces=block_gadgets(n,edges,pairs)
    assert sorted(e for piece in pieces for e in piece.original_ids)==list(range(len(edges)))
    block_rows=[]
    for piece in pieces:
        assert tuple(piece.chords)==chords
        block_rows.extend(piece.project(w) for w in matchings(piece.vertices,piece.edges))
        block_rows.extend(coords(1<<e,chords) for e in piece.loops)
    assert span(block_rows)==annihilators
    rows=[even[1<<i] for i in range(len(chords))]
    columns=[sum(((r>>e)&1)<<j for j,r in enumerate(rows)) for e in range(len(edges))]
    oriented=[span(columns[p[b]] for p,b in zip(pairs,side)) for side in product((0,1),repeat=len(pairs))]
    for t in range(1<<len(chords)):
        assert all(t in space for space in oriented)==all((t&a).bit_count()%2==0 for a in annihilators)
    return chords,annihilators


def main():
    check(0,[],[])
    check(3,[(0,1),(1,2)],[(0,1)])
    check(1,[(0,0),(0,0)],[(0,1)])
    check(3,[(0,0),(0,1),(1,2),(2,0)],[(0,1),(2,3)])
    check(2,[(0,1),(1,0),(0,1),(0,1)],[(0,1),(2,3)])
    check(4,[(0,1),(0,2),(2,1),(0,3),(3,1),(2,2)],[(0,1),(2,4)])
    ch,space=check(5,[(0,1),(1,2),(2,0),(0,3),(3,4),(4,0)],[(0,3)])
    assert len(ch)==2 and len(space)==4
    print('raw Eulerian supports, perfect matchings, all orientations and signed targets checked')


if __name__=='__main__':main()
