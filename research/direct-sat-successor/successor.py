"""Exact original-input circuit SAT with optional prefix and implicit automata stages."""
import argparse
import json
from pathlib import Path
import sys
from time import perf_counter_ns

sys.path.insert(0, str(Path(__file__).resolve().parent / 'lib'))
import portfolio
import implicit_wire_circuit
import prefix_portfolio
from original_cnf import compile_cnf


def solve(n, gates, output, *, schedule=('normalized','raw'), prefix_budget=2_000_000,
          automata_budget=250_000, rank_cap=24, order=None, **portfolio_options):
    start = perf_counter_ns()
    original = portfolio.validate(n, gates, output)
    schedule = tuple(schedule)
    if len(set(schedule)) != len(schedule) or any(k not in ('raw','normalized') for k in schedule):
        raise ValueError('invalid automata schedule')
    for name, value in [('prefix_budget',prefix_budget),('automata_budget',automata_budget),('rank_cap',rank_cap)]:
        portfolio.natural(name, value)
    if order is not None:
        order = tuple(order)
        if sorted(order) != list(range(n)):
            raise ValueError('invalid input bit order')
    m = len(original)
    raw = original, output
    compiled = None
    proxy = m*(n+m+1)**2
    cost = dict(raw_n=n, original_ands=m, schedule=schedule, attempts=[],
                automata_budget_per_attempt=automata_budget, rank_cap=rank_cap,
                raw_bit_order=order, prefix=dict(proxy=proxy,budget=prefix_budget,applied=False),
                input_hex_json_bytes=len(json.dumps([hex(n),[[hex(a),hex(b)] for a,b in original],hex(output)],
                                                      separators=(',',':'))),
                original_replay_evaluations=0)
    def normalize():
        nonlocal compiled
        if compiled is None:
            tick=perf_counter_ns()
            if m and output.bit_length()>n+1 and proxy<=prefix_budget:
                g,y=prefix_portfolio.normalize(n,original,output)
                compiled=tuple(g), y
                cost['prefix']['applied']=True
            else:
                compiled=raw
            cost['prefix'].update(ands=len(compiled[0]),elapsed_ns=perf_counter_ns()-tick)
        return compiled

    def finish(result, route):
        w=result.get('witness')
        if result['status']=='sat':
            if type(w) is not int or not 0<=w<1<<n or not portfolio.evaluate(n,original,output,w):
                raise RuntimeError('raw witness failed untouched original replay')
            cost['original_replay_evaluations']=1
        elif result['status']!='unsat':
            raise RuntimeError('unexpected terminal result')
        cost['elapsed_ns']=perf_counter_ns()-start
        return dict(status=result['status'],witness=w,verified=result['status']=='sat',route=route,cost=cost)

    attempted=set()
    for kind in schedule:
        G,y=raw if kind=='raw' else normalize()
        rec=dict(stage=kind,ands=len(G))
        cost['attempts'].append(rec)
        if y.bit_length()<=n+1:
            bits=y>>1
            w=0 if y&1 else (bits&-bits or None)
            rec['status']='affine'
            return finish(dict(status='sat' if w is not None else 'unsat',witness=w), kind+'_affine')
        if (G,y) in attempted:
            rec['status']='same_presentation'
            continue
        attempted.add((G,y))
        tick=perf_counter_ns()
        try:
            result=implicit_wire_circuit.solve(n,G,y,order=order,budget=automata_budget,rank_cap=rank_cap)
        except TimeoutError:
            result=dict(status='timeout')
        rec.update(status=result['status'],cost=result.get('cost',{}),elapsed_ns=perf_counter_ns()-tick)
        if result['status'] in ('sat','unsat'):
            return finish(result,kind+'_automata')
        if result['status'] not in ('skip','unknown','timeout'):
            raise RuntimeError('unrecognized automata status')
    G,y=normalize()
    result=portfolio.solve(n,G,y,**portfolio_options)
    cost['portfolio']=result['cost']
    return finish(result,'portfolio/'+result['route'])


if __name__=='__main__':
    if hasattr(sys,'set_int_max_str_digits'):
        sys.set_int_max_str_digits(0)
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('path')
    p.add_argument('--schedule',nargs='*',choices=['normalized','raw'],default=['normalized','raw'])
    p.add_argument('--automata-budget',type=int,default=250000)
    p.add_argument('--rank-cap',type=int,default=24)
    p.add_argument('--prefix-budget',type=int,default=2000000)
    p.add_argument('--budget',type=int,default=4096)
    p.add_argument('--rewrite-budget',type=int,default=8)
    args=vars(p.parse_args())
    with open(args.pop('path'),encoding='utf8') as inp:
        data=json.load(inp)
    if 'clauses' in data:
        g,y=compile_cnf(data['n'],data['clauses'])
        data=dict(n=data['n'],gates=g,output=y)
    print(json.dumps(solve(**data,**args),sort_keys=True))
