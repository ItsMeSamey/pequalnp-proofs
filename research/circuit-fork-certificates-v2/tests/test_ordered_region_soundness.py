#!/usr/bin/env python3
"""Check each ordered-region clause against assignments from actual monotone DAGs."""
import itertools
import sys
from pathlib import Path
from collections import Counter, defaultdict
sys.path.insert(0,str(Path(__file__).resolve().parent.parent/'engine'))
from ordered_region import encode_ordered


def model(n,gates):
    root=n+len(gates)-1
    consumers=defaultdict(list)
    useful={root}
    for w in range(root,n-1,-1):
        if w in useful:
            _,a,b=gates[w-n]
            useful.update((a,b))
            consumers[a].append(w)
            consumers[b].append(w)
    regions=sorted(w for w in useful if w==root or len(consumers[w])>1)
    region_id={w:i for i,w in enumerate(regions)}
    for w in sorted(useful,reverse=True):
        if w not in region_id:
            parent,=consumers[w]
            region_id[w]=region_id[parent]
    colors=[region_id.get(i,len(regions)-1) for i in range(n)]
    rows={}
    for x in range(1<<n):
        vals=[(x>>i)&1 for i in range(n)]
        for op,a,b in gates:
            vals.append(vals[a]&vals[b] if op==0 else vals[a]|vals[b])
        trace={root}
        for w in range(root,n-1,-1):
            if w in trace:
                op,a,b=gates[w-n]
                # At AND=true or OR=false both branches are needed.
                if vals[w]!=op:
                    trace.update((a,b))
                else:
                    trace.add(a if vals[a]==vals[w] else b)
        rows[x]=(vals[root],{i for i in trace if i<n},[vals[w] for w in regions])
    bound=len(useful-set(range(n)))-len(useful&set(range(n)))+2
    if len(regions)>bound:
        raise ValueError('region count exceeds the fanout accounting bound')
    return colors,rows,len(regions)


def assignment(keys,colors,rows):
    result=[False]*(len(keys)+1)
    for key,idx in keys.items():
        tag,x,y=key
        if tag=='color':value=colors[x]==y
        elif tag=='same':value=colors[x]==colors[y]
        elif tag in ('pos','neg'):value=y in rows[x][1]
        elif tag=='true':value=rows[x][2][y]==1
        elif tag=='false':value=rows[x][2][y]==0
        else:raise ValueError('unknown semantic key')
        result[idx]=value
    return result


def first_failure(clauses,values):
    for i,c in enumerate(clauses):
        if not any(values[abs(z)]==(z>0) for z in c):
            return i
    return None


def check(n,gates,stats):
    colors,rows,r=model(n,gates)
    positives=[x for x,(v,*_) in rows.items() if v]
    negatives=[x for x,(v,*_) in rows.items() if not v]
    for high,low in [(positives,negatives),(positives[::2],negatives[1::2])]:
        clauses,keys=encode_ordered(high,low,n,r)
        values=assignment(keys,colors,rows)
        failure=first_failure(clauses,values)
        if failure is not None:
            raise ValueError(f'clause {failure} failed on {n=} {gates=} {high=} {low=}')
        stats['care systems']+=1
        stats['clauses']+=len(clauses)
    stats['DAGs']+=1
    stats['shared DAGs']+=r>1
    stats['nested or multiple forks']+=r>=3


def enumerate_cones(n,limit):
    def visit(g):
        if g:
            yield g
        if len(g)==limit:return
        for a,b in itertools.combinations_with_replacement(range(n+len(g)),2):
            for op in (0,1):
                yield from visit(g+[(op,a,b)])
    yield from visit([])


def mutation_check():
    colors,rows,r=model(2,[(0,0,0),(1,2,1)])
    clauses,keys=encode_ordered([1],[0],2,r)
    values=assignment(keys,colors,rows)
    expected=[-keys['true',1,0],-keys['false',0,0],keys['color',0,0]]
    idx=clauses.index(expected)
    if first_failure(clauses,values) is not None:
        raise ValueError('correct mutation fixture failed')
    clauses[idx]=expected[:2]  # Wrongly require a strictly earlier feature.
    if first_failure(clauses,values)!=idx:
        raise ValueError('strict-order mutation escaped')
    return idx


def main():
    stats=Counter()
    for g in enumerate_cones(2,3):check(2,g,stats)
    for g in enumerate_cones(3,2):check(3,g,stats)
    check(4,[(1,0,1),(0,4,2),(1,4,3),(0,5,6),(1,7,5)],stats)
    check(5,[(0,0,1),(1,5,2),(0,5,3),(1,6,7),(0,6,4),(1,8,9)],stats)
    check(3,[(1,0,1),(0,3,2),(1,4,0),(0,5,3)],stats)
    print(dict(stats),'strict-order mutation rejected at clause',mutation_check())


if __name__=='__main__':
    main()
