from itertools import product
import networkx as nx
from three_colour_core_decision import decide


def brute(g):
    return any(all(w[a]!=w[b] for a,b in g.edges) for w in product(range(3),repeat=len(g)))


def main():
    atlas=[g for g in nx.graph_atlas_g() if len(g)<=6]
    for g in atlas:
        assert decide(g)==brute(g)
    for m in range(4,26):
        assert decide(nx.wheel_graph(m+1))==(m%2==0)
    print(len(atlas),"atlas decisions matched complete enumeration; 22 wheel controls passed")


if __name__=='__main__':
    main()
