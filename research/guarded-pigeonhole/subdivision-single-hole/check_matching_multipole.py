from itertools import product
from matching_multipole import *


def brute_signatures(g,ports):
    edges=[frozenset(e) for e in g.edges]
    used={v:set() for v in g}
    signatures=set()
    def search(i):
        if i==len(edges):
            choices=[set(range(3))-used[v] for v in ports]
            signatures.update(c for c in product(*choices) if local_valid(g,ports,c))
            return
        u,v=edges[i]
        for c in set(range(3))-used[u]-used[v]:
            used[u].add(c);used[v].add(c)
            search(i+1)
            used[u].remove(c);used[v].remove(c)
    search(0)
    return signatures


def test(g,ports,order=None):
    truth=brute_signatures(g,ports)
    totals=Counter()
    for colors in product(range(3),repeat=len(ports)):
        status,w=solve(g,ports,colors,order)
        totals[status]+=1
        if status=='SAT':
            assert colors in truth and valid_coloring(g,ports,colors,w)
        elif status=='UNSAT':assert colors not in truth
        else:assert len(ports)>5
    return totals


if __name__=='__main__':
    checks=0
    for g in nx.graph_atlas_g():
        if not len(g) or not nx.is_connected(g) or not nx.is_bipartite(g) or max(dict(g.degree()).values())>3:continue
        ports=[v for v in g for _ in range(3-g.degree(v))]
        if len(ports)<=5:
            test(g,ports)
            checks+=1
    g=nx.cycle_graph(4)
    g.add_edges_from([(0,4),(1,5)])
    ports=[4,4,5,5,2,3]
    print('six-port totals',test(g,ports,list(range(6))))
    for colors in product(range(3),repeat=6):
        if colors[0]!=0 or colors[2]!=0 or any(colors.count(c)!=2 for c in range(3)):continue
        results=[extend_matching(g,ports,colors,0,matching) for matching in
                 [[(0,1),(2,3)],[(1,2),(3,0)]]]
        if (results[0] is None)!=(results[1] is None):
            print('barrier',ports,colors,[r is not None for r in results])
            break
    else:raise AssertionError('missing barrier')
    print('Exhausted all boundary assignments for',checks,'connected simple atlas multipoles with at most five ports.')

    # Parallel internal edges retain their identities in the recovered assignment.
    for multiplicity in (1,2,3):
        multi=nx.MultiGraph()
        multi.add_edges_from([(0,1)]*multiplicity)
        ports=[0]*(3-multiplicity)+[1]*(3-multiplicity)
        for colors in product(range(3),repeat=len(ports)):
            status,w=solve(multi,ports,colors)
            expected=(local_valid(multi,ports,colors) and
                      set(colors[:3-multiplicity])==set(colors[3-multiplicity:]))
            assert (status=='SAT')==expected and status!='UNKNOWN'
            if expected:assert valid_coloring(multi,ports,colors,w)
    ring=nx.cycle_graph(8)
    pts=list(ring)
    order=list(range(8))
    assert certified_disk_order(ring,pts,order)
    assert not certified_disk_order(ring,pts,[0,2,1,3,4,5,6,7])
    known=brute_signatures(ring,pts)
    shore=shape(ring,pts)
    ntested=0
    for pattern in product(range(3),repeat=8):
        if any(sum(2*shore[v]-1 for v,c in enumerate(pattern) if c==a) for a in range(3)):continue
        signs=[shore[v]^int(c==2) for v,c in enumerate(pattern) if c!=0]
        if len(signs)<4 or any(signs[i]==signs[i-1] for i in range(len(signs))):continue
        status,w=solve(ring,pts,pattern,order)
        assert status!='UNKNOWN' and (status=='SAT')==(pattern in known)
        ntested+=1
    print('Checked three parallel-edge multipoles and',ntested,'balanced alternating eight-port patterns.')
