"""Replay soundness tests and pinned demonstration applications."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import runpy
import sys

ROOT=Path(__file__).resolve().parent
sys.path[:0]=[str(ROOT/'engine'),str(ROOT/'tests')]
from applications.check_source import load_application, require
from fork_certificate import verify_case, verify_optional_family
from region_rup import RupChecker

def verify_upper(m, care):
    impl=m['upper_bound']
    require(type(impl) is dict and set(impl)=={'positive_input_count','gates','output'},'upper-bound witness fields')
    n=impl['positive_input_count']
    require(type(n) is int and n==2 and n==m['interfaces'][0]['wire_count'],'XOR positive input count')
    require(m['id']=='xor2' and m['certificates'][0]['model']==dict(literals=['positive']*n,fixed_cost=0),'XOR positive-wire model')
    gates=impl['gates'];output=impl['output']
    require(type(gates) is list and len(gates)==m['scope']['physical_lower_bound'],'upper-bound gate count')
    require(type(output) is int and 0<=output<n+len(gates),'upper-bound output index')
    arity={'and':2,'or':2,'not':1}
    for i,g in enumerate(gates):
        require(type(g) is list and len(g)>0 and type(g[0]) is str and g[0] in arity,'upper-bound gate opcode')
        require(len(g)==1+arity[g[0]],'upper-bound gate arity')
        require(all(type(pin) is int and 0<=pin<n+i for pin in g[1:]),'upper-bound gate pin')
    for x,t in care.items():
        v=[(x>>i)&1 for i in range(n)]
        for op,*pins in gates:
            if op=='not':r=1-v[pins[0]]
            elif op=='and':r=v[pins[0]]&v[pins[1]]
            else:r=v[pins[0]]|v[pins[1]]
            v.append(r)
        require(v[output]==t,'upper-bound truth table')

def application(path):
    m,fixtures=load_application(path)
    care=fixtures['positive'];n=m['interfaces'][0]['wire_count']
    expected={'positive'} if 'optional-marker' not in fixtures else {'positive','negative','both_live'}
    cases=m['certificates']
    require({c['interface'] for c in cases}==expected and len(cases)==len(expected),'incomplete selector cases')
    if 'optional-marker' in fixtures:
        require(any(care.get(p^(1<<16))==1-y for p,y in care.items()),'selector must be live')
    family=[]
    for c in cases:
        mode=c['interface']; literals=['positive']*n
        if mode!='positive':literals[16]=mode
        require(c['model']==dict(literals=literals,fixed_cost=m['budget']['fixed_physical']) and c['feature_count']==n,'physical model binding')
        raw=(path.parent/c['file']).read_bytes()
        require(sha256(raw).hexdigest()==c['sha256'],'certificate pin')
        cert=json.loads(raw)
        if mode=='both_live':
            require(any(case==dict(positive=0,signed=4,ordered=False,partitions=0) for case in cert['cases']),'four unrestricted fork classes must be impossible')
        family.append(dict(literals=literals,certificate=cert))
        if len(expected)>1:continue
        r=verify_case(care,n,c['model'],cert)
        require(r['total_lower_bound']==m['scope']['physical_lower_bound'],'claimed lower bound')
        print(m['id'],mode,'lower bound',r['total_lower_bound'],'partition counts',r['partition_counts'],flush=True)
    if len(expected)>1:
        lits=['positive']*n;lits[16]='optional'
        r=verify_optional_family(care,n,dict(literals=lits,fixed_cost=m['budget']['fixed_physical']),family)
        require(r['case_count']==3 and r['total_lower_bound']==m['scope']['physical_lower_bound'],'combined optional bound')
        print(m['id'],'optional lower bound',r['total_lower_bound'],[x['partition_counts'] for x in r['cases']],flush=True)
    if 'upper_bound' in m:verify_upper(m,care)
    if m['id']=='canonical21':
        comp=runpy.run_path(str(path.parent/'verify_precone_regions.py'))
        nv,clauses,_=comp['encode'](path.parent/m['sources']['positive']['file'])
        count=RupChecker(nv,clauses).verify(path.parent/'precone-region-5.drup')
        require(count==627,'RUP additions')
        print('Canonical one-NOT operand:',len(clauses),'clauses;',count,'RUP additions.')

def main():
    cli=argparse.ArgumentParser(description=__doc__)
    cli.add_argument('--application',choices=['xor2','canonical21','four19','four20'])
    cli.add_argument('--tests-only',action='store_true')
    a=cli.parse_args()
    require(not (a.application and a.tests_only),'choose tests or an application')
    for line in (ROOT/'SHA256SUMS').read_text().splitlines():
        digest,name=line.split('  ',1)
        require(sha256((ROOT/name).read_bytes()).hexdigest()==digest,'digest '+name)
    if not a.application:
        for script in ('test_xor_upper.py','tiny_engine_soundness.py','tiny_free_complement.py','test_optional_family.py','test_ordered_region_soundness.py'):
            runpy.run_path(str(ROOT/'tests'/script),run_name='__main__')
    if not a.tests_only:
        for name in ([a.application] if a.application else ['xor2','canonical21','four19','four20']):
            application(ROOT/'applications'/name/'application.json')
if __name__=='__main__':main()
