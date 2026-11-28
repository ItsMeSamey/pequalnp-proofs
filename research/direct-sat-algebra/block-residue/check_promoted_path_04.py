"""Test two single-output NAND paths by exhaustive original raw assignments."""
from itertools import combinations, product
from unittest.mock import patch

import promoted_row_csp as solver


def fixture(n, defect):
    gates = []
    def nand(a, b):
        gates.append((a,b))
        return 2*n + len(gates)-1
    def inv(a):
        return nand(a,a)
    def both(a,b):
        return inv(nand(a,b))
    sites = []
    for a in range(0,2*n,2):
        b = a+1
        sites.append([both(x,y) for x,y in product((inv(a),a),(inv(b),b))])
    tests = [nand(sites[i][s], sites[i+1][t]) for i in range(n-1)
             for s,t in product(range(4),repeat=2)
             if ((s==3) ^ (t==3)) != (i==defect)]
    tests.extend((inv(sites[0][3]), inv(sites[-1][3])))
    output = tests[0]
    for test in tests[1:]:
        output = both(output,test)
    return gates, output, sites


def audit(n, defect):
    gates, output, sites = fixture(n, defect)
    models = set()
    for raw in product(range(2),repeat=2*n):
        states = [2*raw[i]+raw[i+1] for i in range(0,2*n,2)]
        good = states[0]!=3 and states[-1]!=3 and all(
            ((a==3) ^ (b==3)) == (i==defect)
            for i,(a,b) in enumerate(zip(states,states[1:])))
        wires = list(raw)
        for a,b in gates:
            wires.append(1-(wires[a]&wires[b]))
        assert bool(wires[output]) == good
        if good:
            models.add(raw)
    assert len(models) == (3**n if defect is None else 0)
    captured = {}
    prepare, relations = solver._prepare, solver._relations
    def observe_prepare(*args):
        result = prepare(*args)
        captured["wires"] = result[1:3]
        return result
    def observe_relations(width,base,tables):
        answer = relations(width,base,tables)
        captured["projection"] = tables,answer
        return answer
    with patch.object(solver,"_prepare",observe_prepare), patch.object(solver,"_relations",observe_relations):
        status, stats, raw = solver.solve(2*n,gates,output=output,max_search=0)
    expanded, aliases = captured["wires"]
    remaining, (domains, graph) = captured["projection"]
    assert len(remaining)==n
    annotations = []
    for table, domain in zip(remaining,domains):
        ports = {abs(l)-1 for l, in table[0]}
        candidates = []
        for i, ids in enumerate(sites):
            refs = [(expanded[aliases[w][0]],aliases[w][1]) for w in ids]
            if {w for w,_ in refs} == ports:
                candidates.append((i,refs))
        assert len(candidates)==1
        site, refs = candidates[0]
        colors = {}
        for s in domain:
            row = {abs(l)-1:int(l>0) for l, in table[s]}
            bits = [row[w]^sign for w,sign in refs]
            assert sum(bits)==1
            colors[s] = bits.index(1)
        assert sorted(colors.values()) == list(range(3 if site in (0,n-1) else 4))
        annotations.append((site,colors))
    assert sorted(i for i,_ in annotations)==list(range(n))
    for i,j in combinations(range(n),2):
        a,left = annotations[i]
        b,right = annotations[j]
        assert (j in graph[i]) == (abs(a-b)==1)
        if j in graph[i]:
            expected = {(s,t) for s,u in left.items() for t,v in right.items()
                        if ((u==3) ^ (v==3)) == (min(a,b)==defect)}
            assert graph[i][j]==expected and graph[j][i]=={(t,s) for s,t in expected}
    assert stats["initial_bad"]>stats["bad"]==n
    assert (stats["forest_components"],stats["cyclic_components"],stats["searched"])==(1,0,0)
    if models:
        assert status=="sat" and raw in models
    else:
        assert status=="unsat" and raw is None


if __name__=="__main__":
    for defect in (None,0):
        audit(3,defect)
    print("two original NAND paths, 128 raw words; domains, edges and forest checked")
