"""04-only direct original-bit replay of the indexed fallback on a signed P4."""
from itertools import product
from biclique_physical import UnsupportedConflict, biclique_comparison_witness
from biclique_total import total_block_witness, total_comparison_witness


def run(endpoint_target):
    # A and D are constants; B and C are opposite requests on reversed endpoints.
    # The conflict graph A-B-C-D stays an induced P4 in both cases.
    A=(0,0,1)
    B=(0,1,0)
    C=(1,0,1)
    D=(1,1,endpoint_target)
    edges=[A,B,B,C,C,D]
    try:
        biclique_comparison_witness(2,edges)
    except UnsupportedConflict:
        pass
    else:
        raise AssertionError('this case must exercise the indexed fallback')

    def geometric(w):
        good=[(w[x]^w[y])==d for x,y,d in edges]
        return all(good[i] or good[i+1] for i in range(0,6,2))

    words=[w for w in product((0,1),repeat=2) if geometric(w)]
    result=total_comparison_witness(2,edges)
    assert bool(words)==(endpoint_target==0)==(result is not None)
    if result is not None:assert tuple(result) in words

    # Independent raw encoding; every endpoint occurrence is a fresh bit.
    first={}; pins=[]
    for e,(a,b,d) in enumerate(edges):
        j=4*(e//2)+e%2
        for name,site,phase in ((a,j,0),(b,j+2,1^d)):
            root,offset=first.setdefault(name,(site,phase))
            if site!=root:pins.append((root,site,offset^phase))
    pins.append(pins[0])
    def physical(w):
        return (all((w[i]^w[j])==p for i,j,p in pins)
                and all(w[i:i+2]!=w[i+2:i+4] for i in (0,4,8)))
    raw=[w for w in product((0,1),repeat=12) if physical(w)]
    answer=total_block_witness(3,pins)
    assert bool(raw)==bool(words)==(answer is not None)
    if answer is not None:assert tuple(answer) in raw
    i,j,p=pins[0]
    assert total_block_witness(3,pins+[(j,i,p^1)]) is None


if __name__=='__main__':
    run(0)
    run(1)
    print('opposite-signed induced P4: both verdicts, 8192 raw words, conflicting pins')
