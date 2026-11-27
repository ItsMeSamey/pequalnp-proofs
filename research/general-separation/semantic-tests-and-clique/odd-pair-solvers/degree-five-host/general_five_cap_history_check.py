"""Replay complete accepted four-cap histories after real remote-edge contamination."""
from general_five_cap_host import boundaries, find, first_conflict, moves, odd, recover, terminals, trace_graph
from general_five_cap_host_check import deep_template


def replay(kind, retained):
    graph,pins,path,end=deep_template(1040,kind)
    initial=path[0][6]
    expected,labels,_=trace_graph(graph,pins,initial,path,end)
    target=pins[int(retained)]
    X=next(v for v in reversed(labels) if len(graph[v])<5)
    graph[target].add(X)
    graph[X].add(target)
    abstract,images,_=trace_graph(graph,pins,initial,path,end)
    assert abstract==expected and images==labels
    pos,contacts=first_conflict(graph,abstract,images)
    assert images[pos]==X and {images[i] for i in contacts}=={target}
    assert initial in boundaries(graph,pins,set(pins),set(),set(),set())
    state=(pins,initial,(),())
    for cap in path:
        state=next(s for s,c in moves(graph,state) if c==cap)
    assert end in terminals(graph,state)
    w=recover(graph,pins,initial,path,end)
    assert odd(graph,w,pins)
    return len(w)


if __name__=='__main__':
    for kind,retained in [('A',False),('N',False),('N',True)]:
        print(kind,'retained' if retained else 'deleted',replay(kind,retained))
    g,p,_,_=deep_template(1040,'N')
    w=find([sorted(r) for r in g],p)
    assert w['status']=='YES' and len(w['witness'])==len(g)
    print('whole search, clean',len(g))
