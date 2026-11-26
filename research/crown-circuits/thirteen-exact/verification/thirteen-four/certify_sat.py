from itertools import combinations
from pysat.formula import IDPool
from pysat.solvers import Cadical195
from pysat.card import CardEnc
from pathlib import Path
import os,subprocess,sys
def certify(tags,nc,base):
    p=4; raw=[]; labels=[]
    for t in tags:
        i=len(raw)
        labels.append(t if t.bit_count()==2 else t|(1<<(p+i)))
        if t.bit_count()!=2:raw.append(2-t.bit_count())
    jobs=[((i,),False) for i in range(len(labels))]+[(ij,True) for ij in combinations(range(len(labels)),2)]
    counts=[2-nc,*raw]; n=sum(counts); names=IDPool();cnf=[]
    types=[[names.id(('type',i,k)) for k in range(len(counts))] for i in range(n)]
    for r in types:cnf.extend(CardEnc.equals(r,1,vpool=names).clauses)
    for j,k in enumerate(counts):cnf.extend(CardEnc.equals([r[j] for r in types],k,vpool=names).clauses)
    def prod(slot,t,prev,mask):
        bad=[names.id(('const0',slot))]
        for j in range(4-nc+len(prev)):
            sel=names.id(('sel',slot,j))
            if j<4-nc:
                if not (mask>>j&1):bad.append(sel)
            else:
                w=prev[j-4+nc];q=names.id(('penalty',slot,j,t))
                cnf.extend([[-q,sel],[-q,-w],[q,-sel,w]]);bad.append(q)
        z=names.id(('prod',slot,t))
        cnf.extend([[-z,-a] for a in bad]);cnf.append([z,*bad]);return z
    for t,(inds,want) in enumerate(jobs):
        mask=0
        for i in inds:mask|=labels[i]
        prev=[]
        for i,r in enumerate(types):
            x=prod(2*i,t,prev,mask);y=prod(2*i+1,t,prev,mask)
            z=names.id(('z',i,t));prev.append(z);k=r[0]
            cnf.extend([[-k,-x,z],[-k,-y,z],[-k,x,y,-z]])
            for j,k in enumerate(r[1:]):
                cnf.extend([[-k,z]] if mask>>(4+j)&1 else [[-k,-x,z],[-k,x,-z]])
        out=[prod(2*n,t,prev,mask)]
        for j in range(nc):
            if mask>>(4-nc+j)&1:out.append(prod(2*n+1+j,t,prev,mask))
        cnf.extend([out] if want else [[-k] for k in out])
    with Cadical195(bootstrap_with=cnf,with_proof=True) as s:
        if s.solve():return False
        base.with_suffix('.cnf').write_text(f'p cnf {names.top} {len(cnf)}\n'+''.join(' '.join(map(str,c))+' 0\n' for c in cnf));base.with_suffix('.drat').write_text('\n'.join(s.get_proof())+'\n')
    out=subprocess.check_output([os.environ.get('DRAT_TRIM','drat-trim'),str(base.with_suffix('.cnf')),str(base.with_suffix('.drat'))])
    assert b's VERIFIED' in out
    return True
if __name__=='__main__':
    import hashlib
    proofs=Path('proofs');proofs.mkdir(exist_ok=True)
    files=sys.argv[1:] or ['clean2.log','clean.log','onesat.log']
    cases=set()
    for f in files:
        for l in open(f):
            if l.startswith('X '):
                before,tags=l.split('|');cases.add((int(before.split()[3]).bit_count(),tuple(map(int,tags.split()))))
    for c,tags in sorted(cases,key=lambda r:(len(r[1]),r)):
        stem=str(c)+'_'+'_'.join(map(str,tags))
        assert certify(tags,c,proofs/stem),stem
        print(stem,'verified',flush=True)
