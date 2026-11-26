"""Run the complete finite verification in a temporary working directory."""
import argparse
import itertools
import os
import pickle
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT=Path(__file__).resolve().parent
def script(name,*args,expect=None):
    result=subprocess.run([sys.executable,str(ROOT/name),*map(str,args)],text=True,capture_output=True,check=True)
    if expect and expect not in result.stdout:raise RuntimeError(f'{name} missing {expect}: {result.stdout}')
    print(result.stdout.rstrip(),flush=True)

def main():
    parser=argparse.ArgumentParser()
    parser.add_argument('--stages',default='geometry,five,four-marked,six,seven19,seven20')
    parser.add_argument('--strong',action='store_true',help='use the additional proved count cuts for final cases')
    cfg=parser.parse_args()
    stages=set(cfg.stages.split(','))
    if 'geometry' in stages:
        script('geometry.py');script('atlas_audit.py');script('audit_six.py')
    if 'five' in stages:script('five_certificate/verify.py',expect='Both marked minima')
    if 'four-marked' in stages:
        for geom in ('0123','0124'):script('marked_four.py',geom,13,expect='\nFalse ')
    from role_general import run,possibilities
    if 'six' in stages:
        for geom in ('012345','012346'):
            ns=tuple(map(int,geom))
            lines=[{(i+d)%13 for d in (0,1,3,9)} for i in ns]
            for triple in itertools.combinations(range(6),3):
                if set.intersection(*(lines[t] for t in triple)):
                    script('roles.py',geom,''.join(map(str,triple)),expect='\nFalse ')
            jobs=list(possibilities(ns,17))
            assert len(jobs)=={'012345':66,'012346':164}[geom]
            for S,G,v,Q,dd in jobs:assert run(ns,S,G,v,Q,dd)[0] is False
            print('six-line 17-gate exclusions',geom,len(jobs),flush=True)
    ns=tuple(range(7))
    if 'seven19' in stages:
        jobs=[job for job in possibilities(ns,19) if not job[0]]
        assert len(jobs)==16
        for S,G,v,Q,dd in jobs:assert run(ns,S,G,v,Q,dd)[0] is False
        print('seven-line 19-gate exclusions',len(jobs),flush=True)
    if 'seven20' not in stages:return
    from graph7 import alljobs
    jobs=list(alljobs())
    assert len(jobs)==8128
    Path('seven-jobs.pkl').write_bytes(pickle.dumps(jobs))
    script('writefilter.py')
    subprocess.run(['g++','-std=c++20','-O3',str(ROOT/'filter7.cpp'),'-o','filter7'],check=True)
    with open('filter7.in','rb') as ip,open('filter7.out','wb') as op:
        subprocess.run(['./filter7'],stdin=ip,stdout=op,check=True)
    done={};viable={}
    for row in Path('filter7.out').read_text().splitlines():
        i,d,g,h=map(int,row.split())
        if g>=0:continue
        assert d not in done.setdefault(i,set())
        done[i].add(d)
        if h:viable.setdefault(i,set()).add(d)
    simple=interval=checked=0
    if cfg.strong:from role_strong import run as final_run
    else:final_run=run
    for i,(S,G,v,Q,dd) in enumerate(jobs):
        if Q==2:
            neighbor=[{t for t,e in G.items() if vertex in e} for vertex in range(v)]
            pure=[u for u in neighbor if u<=set(S)]
            if not any(x.isdisjoint(y) for x in pure for y in pure):simple+=1;continue
            assert done[i]==set(range(len(dd)))
            if i not in viable:interval+=1;continue
            dd=[dd[j] for j in sorted(viable[i])]
        assert final_run(ns,S,G,v,Q,dd)[0] is False,(i,S,G,v,Q,dd)
        checked+=1
        if checked%100==0:print('verified final SAT cases',checked,flush=True)
    assert (simple,interval,checked)==(3070,3971,1087)
    print('Seven-line exact minimum 21. Final coverage:',simple,interval,checked,flush=True)

if __name__=='__main__':
    with tempfile.TemporaryDirectory() as tmp:
        os.chdir(tmp);main()
