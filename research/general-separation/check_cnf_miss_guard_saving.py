"""Identical-input finite saving; the fourteen equal-scope guard columns are twins."""
from itertools import combinations
from cnf_miss_span import solve


def main():
    guards=tuple(range(5,19))
    rows=[guards+tuple(-v if bit>>i&1 else v for i,v in enumerate(pair))
          for pair in combinations(range(1,5),2) for bit in (1,2,3)]
    rows.append(tuple(-v for v in guards))
    assert len(rows)==19
    assert not any(set(c)<=set(d) for c in rows for d in rows if c!=d)
    # Direct partition by three disjoint guard cases; inspect all 16 data words.
    expected=0
    for true_guards,multiplicity in [(set(),1),({5},(1<<14)-2),(set(guards),1)]:
        for word in range(16):
            selected=true_guards|{i+1 for i in range(4) if word>>i&1}
            expected+=multiplicity*all(any((abs(l) in selected)==(l>0) for l in c) for c in rows)
    assert expected==((1<<14)-2)*16+1
    ans=solve(18,rows)
    assert ans['status']=='nonzero' and ans['count']==(expected,0)
    assert ans['mode']=='inclusion_exclusion' and ans['rank']<=11
    assert 0<ans['terms']<=19*(1<<11)<min(1<<18,1<<19)
    selected=set(ans['true_ids'])
    assert all(any((abs(l) in selected)==(l>0) for l in c) for c in rows)
    print('Guard fixture count',expected,'rank',ans['rank'],'terms including lift',ans['terms'])


if __name__=='__main__':
    main()
