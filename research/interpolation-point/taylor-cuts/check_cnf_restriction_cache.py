from itertools import product
from random import Random
from cnf_restriction_cache import RestrictionCache,replay_unsat


def main():
    rng = Random(912)
    cache = RestrictionCache()
    for _ in range(100):
        n=rng.randrange(1,6)
        rows=[[rng.choice((-1,1))*rng.randrange(1,n+1) for _ in range(rng.randrange(1,4))]
              for _ in range(rng.randrange(8))]
        pins={i:rng.randrange(2) for i in range(1,n+1) if rng.randrange(3)==0}
        expected=[m for m in range(1<<n) if all((m>>(i-1)&1)==b for i,b in pins.items()) and
                  all(any((m>>(abs(x)-1)&1)==(x>0) for x in row) for row in rows)]
        witness,key=cache.query(n,rows,pins)
        assert witness in expected if expected else witness is None
        if not expected:
            assert replay_unsat(rows,pins,cache.certificate(n,rows,pins))
    rows=list(product((1,-1),(2,-2),(3,-3)))
    witness,key=cache.query(3,rows)
    assert witness is None and replay_unsat(rows,{},cache.certificate(3,rows))
    renamed=[[(7 if x<0 else -7) if abs(x)==1 else (1 if x>0 else -1)*(5 if abs(x)==2 else 2)
              for x in row] for row in reversed(rows)]
    before=len(cache.unsat)
    assert cache.query(8,renamed,{8:1})==(None,key) and len(cache.unsat)==before
    assert replay_unsat(renamed,{8:1},cache.certificate(8,renamed,{8:1}))
    root,label,proof=cache.certificate(3,rows)
    broken=dict(proof)
    split,(child,edge_label),edge=broken[root]
    broken[root]=(split,(child,(edge_label[0],)*len(edge_label)),edge)
    assert not replay_unsat(rows,{},(root,label,broken))
    assert not replay_unsat(rows,{},(root,(1,1,1),proof))
    del broken[root]
    assert not replay_unsat(rows,{},(root,label,broken))
    asymmetric=[(1,),(-1,2),(-2,3),(-3,)]
    cert=cache.certificate(3,asymmetric)
    root,label,proof=cert
    assert not replay_unsat(asymmetric,{},(root,(-label[0],*label[1:]),proof))
    flipped_rejected=False
    for key,node in proof.items():
        for j in range(1,len(node)):
            child,edge_label=node[j]
            for i in range(len(edge_label)):
                altered=edge_label[:i]+(-edge_label[i],)+edge_label[i+1:]
                bad=dict(proof)
                bad[key]=node[:j]+((child,altered),)+node[j+1:]
                flipped_rejected |= not replay_unsat(asymmetric,{},(root,label,bad))
    assert flipped_rejected
    # A verifier must accept while the producer's expensive primitive is disabled.
    import cnf_restriction_cache as module
    from unittest.mock import patch
    with patch.object(module,"canonical",side_effect=AssertionError("producer-only")):
        assert replay_unsat(asymmetric,{},cert)
    print("100 brute controls; signed labeled DAG replay, invalid roots/edges and no-canonicalizer replay passed")


if __name__=="__main__":
    main()
