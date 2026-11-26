"""Checkpointable iterative DFS. Cursor counts include rejected consistency tests."""
import argparse
from collections import Counter
from itertools import islice
import json, os, resource, time
from pathlib import Path
from search_rows import P,V,coefficients,insert,patterns
from lift_witness import lift

def row_order(n):
    from itertools import combinations
    from functools import reduce
    from operator import xor
    if n!=9:return list(range(1<<n))
    # Each consecutive triple is one block-rotation orbit.
    basis=[31,248,451,61,488,327,39,312,452]
    order=[0]+basis+[a^b for a,b in combinations(basis,2)]
    for weight in range(3,10):
        rows={reduce(xor,terms) for terms in combinations(basis,weight)}
        groups=[[],[]]
        while rows:
            v=min(rows); w=((v<<3)&511)|(v>>6); z=((w<<3)&511)|(w>>6)
            orbit=sorted({v,w,z})
            rows.difference_update(orbit)
            negative=sum((v>>(3*i)&7)==7 for i in range(3))%2
            groups[negative].append(orbit)
        while any(groups):
            for group in groups:
                if group:order.extend(group.pop())
    assert sorted(order)==list(range(512))
    return order

def run(n,r,target,destination,seconds,step_limit=None,joint_pauli_cut=False):
    if joint_pauli_cut:
        from joint_z_cut import rejects
        expected=[(-1)**sum((x>>(3*i)&7)==7 for i in range(3)) for x in range(512)]
        if n!=9 or r!=7 or list(target)!=expected:
            raise ValueError('joint Pauli cut requires the three-block target and rank seven')
    started=time.monotonic()
    order=row_order(n)
    if destination.exists():
        data=json.loads(destination.read_text())
        if data['target']!=target or data['r']!=r or data['order']!=order:raise ValueError('checkpoint target mismatch')
        if data['status']!='UNKNOWN':return data
    else:
        data=dict(target=target,r=r,order=order,status='UNKNOWN',path=[],cursors=[0],nodes=1,
                  tested=0,rejected=0,closed=0,max_depth=0,elapsed=0.,accepted_by_depth={})
    cols=[{} for _ in range(r)]
    path=[];stack=[]
    def frame(x,basis,cursor=0):
        sol=coefficients(basis,r)
        rhs=(target[order[x]]%P,0)
        # patterns computes domains using the shared columns before yielding.
        it=iter(patterns(n,cols,order[x],sol,rhs))
        for _ in islice(it,cursor):pass
        return [basis,sol,rhs,it,cursor]
    basis={}
    for x,pat in enumerate(data['path']):
        stack.append(frame(x,basis,data['cursors'][x]))
        basis=insert(basis,[V[v] for v in pat]+[(target[order[x]]%P,0)])
        if basis is None:raise ValueError('inconsistent checkpoint prefix')
        for c,v in zip(cols,pat):c[order[x]]=v
        path.append(pat)
    stack.append(frame(len(path),basis,data['cursors'][-1]))
    tested_before=data['tested']
    while stack and time.monotonic()-started<seconds:
        if step_limit is not None and data['tested']-tested_before>=step_limit:break
        x=len(path)
        basis,sol,rhs,it,off=stack[-1]
        pat=next(it,None)
        if pat is None:
            stack.pop();data['closed']+=1
            if path:
                path.pop()
                for c in cols:del c[order[x-1]]
            continue
        stack[-1][-1]+=1;data['tested']+=1
        new=insert(basis,[V[v] for v in pat]+[rhs]) if sol is None else basis
        if new is None:
            data['rejected']+=1
            continue
        path.append(pat)
        for c,v in zip(cols,pat):c[order[x]]=v
        if joint_pauli_cut and rejects(cols):
            path.pop()
            for c in cols:del c[order[x]]
            data['joint_pauli_rejected']=data.get('joint_pauli_rejected',0)+1
            continue
        data['nodes']+=1
        key=str(x)
        data['accepted_by_depth'][key]=data['accepted_by_depth'].get(key,0)+1
        data['max_depth']=max(data['max_depth'],x+1)
        if x+1==len(target):
            weights=lift(cols,target)
            if weights is None:raise AssertionError('field false positive')
            data['status']='SAT';data['weights']=[[str(a),str(b)] for a,b in weights]
            break
        stack.append(frame(x+1,new))
    if not stack:data['status']='UNSAT'
    data['path']=path
    data['cursors']=[f[-1] for f in stack]
    data['elapsed']+=time.monotonic()-started
    data['max_rss_kib']=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss
    temp=destination.with_suffix('.tmp')
    temp.write_text(json.dumps(data,sort_keys=True))
    os.replace(temp,destination)
    return data

if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--blocks',type=int,choices=[1,2,3],required=True)
    parser.add_argument('--rank',type=int,choices=range(1,8),required=True)
    parser.add_argument('--seconds',type=float,default=15.)
    parser.add_argument('--checkpoint',type=Path,required=True)
    parser.add_argument('--step-limit',type=int)
    parser.add_argument('--joint-pauli-cut',action='store_true')
    args=parser.parse_args()
    n=3*args.blocks
    target=[(-1)**sum((x>>(3*i)&7)==7 for i in range(args.blocks)) for x in range(1<<n)]
    result=run(n,args.rank,target,args.checkpoint,args.seconds,args.step_limit,args.joint_pauli_cut)
    fields=['status','nodes','tested','rejected','closed','max_depth','elapsed','max_rss_kib','accepted_by_depth','cursors']
    print(json.dumps({k:result[k] for k in fields},sort_keys=True))
