"""04-only direct checks of signed clause gadgets, raw copies and original NANDs."""
from itertools import permutations, product
from cnf_shell import compile_cnf, cnf_witness
from cnf_shell_dispatch import cnf_dispatch_witness
from check_branch_nand_04 import physical_source, replay


def truth(x,c):
    return any(x[abs(l)-1]^(l<0) for l in c)


def valid(chart,w):
    return (all((w[a]^w[b])==s for a,b,s in chart.pins)
            and all(w[i:i+2]!=w[i+2:i+4] for i in range(0,len(w),4)))


def one(c,encoding):
    chart=compile_cnf(3,[c],encoding=encoding)
    assert chart.shells==2 and len(chart.ports)==8
    source=physical_source(2,chart.pins,suffix=3)
    chains={}
    for i,(v,d) in enumerate(chart.ports):chains.setdefault(v,[]).append((i,d))
    pins={(a,b,s^t) for chain in chains.values() for (a,s),(b,t) in zip(chain,chain[1:])}
    assert set(chart.pins)==pins and len(chart.pins)==len(pins)
    for x in product((0,1),repeat=3):
        a,b,e=[x[abs(l)-1]^(l<0) for l in c+(c[-1],)*(3-len(c))]
        good=0
        for z,rail in product((0,1),repeat=2):
            p=[rail,*(rail^v for v in x),rail^z]
            w=tuple(p[v]^off for v,off in chart.ports)
            if encoding=='centered':
                local=(len({a,b,z})>1 and len({1^z,e,0})>1)
            else:
                local=bool((a or (z^b)) and (b or (z^e^1)))
            assert valid(chart,w)==local and bool(replay(source,(*w,0,1,0,w[0])))==local
            if local:
                decoded=chart.decode(w)
                assert all(decoded[abs(l)-1]==x[abs(l)-1] for l in c)
            if not rail:good+=local
        double=(a!=b and e==1) if encoding=='centered' else a==b==1
        assert good==(1+int(double) if truth(x,c) else 0)
        lifted=chart.lift(x)
        assert (lifted is not None)==bool(good)
        if good:assert valid(chart,tuple(lifted))


def formula(n,cs,encoding):
    models={x for x in product((0,1),repeat=n) if all(truth(x,c) for c in cs)}
    dispatched=cnf_dispatch_witness(n,cs,encoding=encoding)
    assert (dispatched is not None)==bool(models)
    if dispatched is not None:assert tuple(dispatched) in models
    answer=cnf_witness(n,cs,encoding=encoding)
    assert (answer is not None)==bool(models)
    if answer is not None:assert tuple(answer) in models
    chart=compile_cnf(n,cs,encoding=encoding)
    if chart is None:
        assert not models
        return
    for x in product((0,1),repeat=n):
        w=chart.lift(x)
        assert (w is not None)==(x in models)
        if w is not None:assert valid(chart,tuple(w)) and tuple(chart.decode(w)) in models
    if answer is not None and cs:
        w=chart.lift(answer)
        assert replay(physical_source(chart.shells,chart.pins,suffix=3),(*w,1,0,1,w[0]))


def main():
    for enc in ('direct','centered'):
        for order in permutations((1,2,3)):
            for signs in product((-1,1),repeat=3):
                one(tuple(s*v for s,v in zip(signs,order)),enc)
        for c in [(1,),(-2,),(1,-1),(1,1,-1),(-2,-2,-2)]:one(c,enc)
        chart=compile_cnf(3,[(1,-2,1)],encoding=enc)
        src=physical_source(chart.shells,chart.pins,suffix=3)
        for w in product((0,1),repeat=8):
            ok=valid(chart,w)
            assert bool(replay(src,(*w,0,1,0,w[0])))==ok
            assert not replay(src,(*w,0,0,0,w[0]))
            try:decoded=chart.decode(w)
            except ValueError:assert not ok
            else:assert ok and truth(decoded,chart.clauses[0])
        for n,cs in [(0,[]),(2,[()]),(3,[(1,),(-1,)]),
                     (3,[(1,-2,3),(3,1,-2),(-1,2,-3),(1,-1),(2,2)]),
                     (2,[(1,2),(1,-2),(-1,2),(-1,-2)])]:
            formula(n,cs,enc)
    try:compile_cnf(4,[(1,2,3,4)])
    except ValueError:pass
    else:raise AssertionError('width four accepted')
    print('direct/centered: 106 clause cases, 512 raw words and 10 source formulas')


if __name__=='__main__':main()
