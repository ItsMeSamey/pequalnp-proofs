from pathlib import Path
from random import Random
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[1]/'mixed-ternary-native'))
from compiler import compile_cnf,decode
from solver import solve


def accepts(rows,word):
    return all(any(bool(word>>(abs(l)-1)&1) == (l>0) for l in row) for row in rows)


def verify(n,rows,mode):
    expected={w for w in range(1<<n) if accepts(rows,w)}
    N,cs,selectors=compile_cnf(n,rows,pin_selectors=mode)
    result=solve(N,cs,b=n,extract_arities=(3,),exponent_cap=0,
                 complete=False,orient=True,detect_blocks=True)
    assert result['status']==('sat' if expected else 'unsat'), (rows,result)
    if expected:
        w=result['witness']
        assert accepts(cs,w) and decode(w,selectors) in expected
        if mode:
            assert decode(w,selectors)==sum((w>>(r-1)&1)<<i for i,(_,_,r) in enumerate(selectors))
    return N,len(cs)


if __name__=='__main__':
    rng=Random(243951)
    cases=[(0,[]),(0,[()]),(1,[]),(2,[()]),(1,[(1,),(-1,)]),
           (3,[(1,-1,2,3),(2,2,-3),(-3,)])]
    for n in (1,2,3):
        for _ in range(5):
            cases.append((n,[tuple(rng.choice((-1,1))*rng.randint(1,n)
                              for _ in range(rng.randint(1,5))) for _ in range(rng.randint(1,4))]))
    sizes=[verify(n,rows,pin) for n,rows in cases for pin in (False,True)]
    print(len(sizes),'exact source decisions; largest physical',max(sizes))
