from random import Random
from orbit_subcube import *
rng=Random(869)
count=0
for n in range(7):
    for _ in range(30):
        clauses=[tuple(rng.choice((-1,1))*rng.randint(1,n) for _ in range(rng.randrange(4))) if n else ()
                 for _ in range(rng.randrange(8))]
        I=encode(n,clauses)
        seen={I.start:''};q=[I.start]
        for v in q:
            for c,g in (('r',I.rotation),('f',I.flip)):
                w=move(g,v)
                if w not in seen:q.append(w);seen[w]=seen[v]+c
        assert len(seen)==1<<n
        expected={x for x in range(1<<n) if all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)}
        assert expected=={decode_witness(n,clauses,word) for v,word in seen.items() if not v&I.zero}
        for x in range(1<<n):
            try:w=encode_witness(n,clauses,x)
            except ValueError:assert x not in expected;continue
            assert x in expected and len(w)<=2*n and decode_witness(n,clauses,w)==x
        count+=1
print(count,'full orbit and source-witness round trips')
wide=reduce_raw(10**100,[(10**99,),(-1,10**98)])
assert len(wide.active)==3 and wide.orbit.dimension==26
word=wide.word_for_true_indices([10**99,10**77])
assert wide.true_indices_for_word(word)=={10**99}
