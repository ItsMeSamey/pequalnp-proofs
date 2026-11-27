"""Check a loop-free simple cubic replacement of each dangling port."""
from itertools import product
from cubic_paired_match_check import contracted, local


def internal_edges():
    # Vertex 4 subdivides the missing edge 01. Edge 23 belongs to triangle 023.
    return [(0,4),(4,1),(0,2),(0,3),(1,2),(1,3),(2,3)]


def check_fragment():
    edges=internal_edges()
    clean=edges[:-1]
    seen={4}
    while True:
        nxt=seen|{b for a,b in clean if a in seen}|{a for a,b in clean if b in seen}
        if nxt==seen:break
        seen=nxt
    assert seen==set(range(5))
    boundary=[]
    for s in (0,1):
        val=0
        for y in product((0,1),repeat=5):
            term=(-2)**sum(y)*local(s,y[4],False,False)
            for a,b in edges:term*=local(y[a],y[b],(a,b)==(2,3),False)
            val+=term
        boundary.append(val)
    assert [v%3 for v in boundary]==[1,2]
    return boundary


def simple_gadget(left,right,logical_edges):
    assert len(set(logical_edges)) == len(logical_edges)
    assert all(0 <= a < left <= b < left + right for a, b in logical_edges)
    n = 0
    new = []
    drift = set()
    unused = []
    logical_ports = {}
    for v in range(left + right):
        outgoing = [e for e in logical_edges if e[0] == v]
        incoming = [e for e in logical_edges if e[1] == v]
        degree = len(outgoing) + len(incoming)
        t = max(1, degree - 2, len(outgoing))
        t += (t + 2 - degree + len(outgoing)) % 2
        chain = [list(range(3*i, 3*i+3)) for i in range(n, n+t)]
        n += t
        for a, b in zip(chain, chain[1:]):
            new.append((a.pop(), b.pop()))
        # Reserve every outgoing port on a distinct block before pooling ports.
        for e, block in zip(outgoing, chain):
            source = block.pop()
            logical_ports[e, v] = source
            drift.add(source)
        free = [port for block in chain for port in block]
        for e in incoming:
            logical_ports[e, v] = free.pop()
        unused.extend(free)
    for e in logical_edges:
        new.append((logical_ports[e, e[0]], logical_ports[e, e[1]]))
    base = len(new)
    for x in unused:
        ports = [list(range(3*i, 3*i+3)) for i in range(n, n+5)]
        n += 5
        new.append((x, ports[4].pop()))
        for a, b in internal_edges():
            i, j = ports[a].pop(), ports[b].pop()
            new.append((i, j))
            if (a, b) == (2, 3):
                drift.add(i)
        assert all(not row for row in ports)
    assert all(sum(3*i+j in drift for j in range(3)) <= 1 for i in range(n))
    assert all(not (a in drift and b in drift) for a, b in new)
    assert sorted(i for pair in new for i in pair)==list(range(3*n))
    block_edges=[tuple(sorted((i//3,j//3))) for i,j in new]
    assert all(i!=j for i,j in block_edges)
    assert len(block_edges)==len(set(block_edges))
    return n,new,drift,base


def check_graph(left,right,edges):
    n,links,drift,base=simple_gadget(left,right,edges)
    actual=contracted(n,links,drift)
    bis=sum(all(not (x>>a&x>>b&1) for a,b in edges) for x in range(1<<(left+right)))
    assert actual%3==((-1)**base*bis)%3
    return n


def check_bases():
    gl=good=0
    for rows in product(range(1,8),repeat=3):
        images={sum(((r&x).bit_count()%2)<<i for i,r in enumerate(rows)) for x in range(8)}
        if len(images)!=8:continue
        gl+=1
        if all(r.bit_count()==1 for r in rows):good+=1
    assert (gl,good)==(168,6)


if __name__=='__main__':
    boundary=check_fragment()
    sizes=[]
    for left,right in ((0,0),(1,0),(1,1),(1,2),(2,2),(2,3)):
        possible=[(i,left+j) for i in range(left) for j in range(right)]
        for bits in range(1<<len(possible)):
            sizes.append(check_graph(left,right,[e for j,e in enumerate(possible) if bits>>j&1]))
    sizes.append(check_graph(1,5,[(0,i) for i in range(1,6)]))
    check_bases()
    print('boundary weights',boundary,'graphs',len(sizes),'largest block count',max(sizes),
          'single-edge-preserving port bases 6/168')
