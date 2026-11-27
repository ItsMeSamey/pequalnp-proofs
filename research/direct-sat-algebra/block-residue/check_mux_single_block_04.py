"""Small private-mux elimination and physical NAND audit for scheduler 04."""
from itertools import product

from matching_nand import compile_source


def make(flip):
    rail = 9
    gates = [(0, 1), (5, 2), (6, 3), (7, 4)]
    shells = []
    for z, (a, b) in enumerate(gates, 5):
        x, y = (b, a) if flip else (a, b)
        shells.extend([((x, rail, 1), (z, rail, 0)),
                       ((x, rail, 0), (z, y, 0))])
    shells.append(((8, rail, 1), (8, rail, 1)))
    roots = [1, 0, 2, 3, 4] if flip else list(range(5))
    connectors = []
    for i, j in enumerate((2, 3, 4, 1)):
        u, v, s, h = roots[i], roots[i+1], roots[j], 10+i
        assert s not in (u, v)
        connectors.extend([((s, rail, 0), (h, u, 0)),
                           ((s, rail, 1), (h, v, 0))])
    return gates, shells, connectors, roots


def accepts(rows, bits):
    return all(any(bits[x]^bits[y]==d for x,y,d in pair) for pair in rows)


def audit_graph(rows, roots):
    edges = [edge for pair in rows for edge in pair]
    graph = [set() for _ in range(14)]
    for a,b,d in edges:
        graph[a].add(b)
        graph[b].add(a)
    assert all(len(graph[v])>=3 for v in roots[1:-1])
    for removed in range(14):
        start = int(removed==0)
        seen = {start}
        stack = [start]
        while stack:
            for v in graph[stack.pop()]-seen-{removed}:
                seen.add(v)
                stack.append(v)
        assert len(seen)==13
    assert sum(len(neighbors-{9}) for i,neighbors in enumerate(graph) if i!=9)==24
    signs = {(min(x,y),max(x,y),d) for x,y,d in edges}
    assert any((x,y,1-d) in signs for x,y,d in signs)


def physical_chart(rows):
    ports = []
    for ((x,y,d),(u,v,f)) in rows:
        ports.extend(((x,0),(u,0),(y,1^d),(v,1^f)))
    last = {}
    pins = []
    for i,(name,offset) in enumerate(ports):
        if name in last:
            j,s = last[name]
            pins.append((i,j,s^offset))
        last[name] = i,offset
    return ports,pins


def main():
    for flip in (False,True):
        gates,core,connect,roots = make(flip)
        rows = core+connect
        audit_graph(rows,roots)
        ports,pins = physical_chart(rows)
        n = 2*len(rows)
        inputs,net,out = compile_source(n,[],[(i,i+1) for i in range(0,n,2)])
        for primary in product((0,1), repeat=5):
            for rail in (0,1):
                values = list(primary)
                for x,y in gates:
                    values.append(((values[x]^rail)&(values[y]^rail))^rail)
                bits = values+[rail]
                choices = [h for h in product((0,1),repeat=4)
                           if accepts(connect,bits+list(h))]
                assert len(choices)==1
                full = bits+list(choices[0])
                proper = all(x!=rail for x in primary)
                assert accepts(rows,full)==proper
                word = [full[v]^s for v,s in ports]+[0,1,0]
                assert len(word)==inputs and all(word[i]^word[j]==s for i,j,s in pins)
                for x,y in net:
                    word.append(1-(word[x]&word[y]))
                assert bool(word[out])==proper
                for internal in product((0,1),repeat=4):
                    assert accepts(core,list(primary)+list(internal)+[rail])==(
                        proper and tuple(values[5:])==internal)
    print("2 orientations, 128 unique connector extensions and original NAND replays, 2048 core assignments")

if __name__=="__main__":
    main()
