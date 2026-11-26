"""Replay higher mixed-gate searches on the ten-point boundary."""
import argparse
from collections import Counter
from functools import lru_cache
from itertools import combinations,combinations_with_replacement
from pathlib import Path
import subprocess
import tempfile
from inputs import raw_samples, actions, records

HERE=Path(__file__).resolve().parent
RAW=tuple(1<<j for j in range(7))

def possible_lines(positive,negative):
    # Each line gate costs one and has a singleton trace given by the
    # intersection or union of its two input traces.
    obligations={(p>>13,n>>13) for p in positive for n in negative if not (p&8191)&~(n&8191)}
    obligations=sorted((p,n) for p,n in obligations if all(p!=q or n==m or n&~m for q,m in obligations))
    covers=[sum(bool(a&p and not a&n)<<i for i,(p,n) in enumerate(obligations)) for a in range(128)]
    all_pairs=(1<<len(obligations))-1
    @lru_cache(None)
    def valid(f):
        mask=0
        for a in f:mask|=covers[a]
        return mask==all_pairs
    data={(0,7):{RAW}};initial={RAW}
    for paid in range(1,4):
        next_programs=set()
        for s in initial:
            new={x|y for x,y in combinations_with_replacement(s,2)}|{x&y for x,y in combinations_with_replacement(s,2)}
            next_programs.update(tuple(sorted((*s,z))) for z in new)
        for line_count in range(8,min(9,7+paid)+1):
            data[paid,line_count]={f for s in next_programs for f in combinations(s,line_count) if valid(f)}
        initial=next_programs
    expected={(1,8):29,(2,8):64,(3,8):99,(2,9):540,(3,9):2069}
    assert all(len(data[key])==n for key,n in expected.items())
    return data

def main():
    ap=argparse.ArgumentParser(description=__doc__)
    for name in ('statement','refined','nine','distinct','duplicate'):
        ap.add_argument(name,type=Path)
    ap.add_argument('--mixed',type=int,choices=range(18,22))
    ap.add_argument('--lines',type=int,choices=(7,8,9))
    ap.add_argument('--cxx',default='c++')
    args=ap.parse_args()
    positive,maximal,negative=raw_samples(args.statement)
    group=actions(positive,maximal)
    nine=records(args.nine,9);assert len(nine)==16924
    extensions={}
    for duplicate,path in [(False,args.distinct),(True,args.duplicate)]:
        for i,x,k in records(path,3):
            assert 1<=i<=len(nine) and duplicate==(x==0 or x in nine[i-1])
            f=tuple(sorted((*nine[i-1],x)))
            extensions[f]=min(k,extensions.get(f,100))
    assert len(extensions)==27786
    point_rel=sorted({(p&8191,n&8191) for p in positive for n in negative if not (p>>13)&~(n>>13)})
    assert len(point_rel)==2961
    with tempfile.TemporaryDirectory() as td:
        tmp=Path(td)
        for name in ('point-cost','frontier'):
            subprocess.run([args.cxx,'-std=c++20','-O3',str(HERE/(name+'.cpp')),'-o',str(tmp/name)],check=True)
        (tmp/'relations').write_text(''.join(f'{p} {n}\n' for p,n in point_rel))
        given=''.join(' '.join(map(str,(*f,k)))+'\n' for f,k in sorted(extensions.items()))
        result=subprocess.run([str(tmp/'point-cost'),str(tmp/'relations')],input=given,text=True,capture_output=True,check=True)
        tightened={}
        for line in result.stdout.splitlines():
            *f,k=map(int,line.split());tightened[tuple(f)]=k
        assert set(tightened)==set(extensions)
        assert Counter(tightened.values())=={15:1365,16:26421}
        all_families=tightened.copy()
        for row in records(args.refined,11):
            key=tuple(sorted(row[:10]));assert key not in all_families
            all_families[key]=row[10]
        assert len(all_families)==27786+23274
        assert min(all_families.values())==12
        line_data=possible_lines(positive,negative)
        def replay(m,L):
            surplus=m-(10+L-1)
            if surplus<0:
                return
            reps=set();case_count=0
            @lru_cache(None)
            def moved_lines(f,idx):
                l=group[idx][1];return tuple(sorted(l[x] for x in f))
            for f,cost in all_families.items():
                available=33-m-cost
                if available<L-7:continue
                assert 0<=available<=3
                fs={RAW} if L==7 else line_data[available,L]
                moves=[tuple(sorted(pm[x] for x in f)) for pm,_ in group]
                best=min(moves);indices=[i for i,x in enumerate(moves) if x==best]
                for ls in fs:
                    case_count+=1
                    rep=min(moved_lines(ls,i) for i in indices)
                    # Reordering within the line side only fixes wire labels.
                    reps.add((*best,*rep))
            if not reps:
                return
            head=[len(positive),len(maximal),*sorted(positive),*sorted(maximal),len(reps),10,L,surplus]
            data=' '.join(map(str,head))+'\n'+''.join(' '.join(map(str,f))+'\n' for f in sorted(reps))
            result=subprocess.run([str(tmp/'frontier')],input=data,text=True,capture_output=True,check=True)
            depths=[int(line) for line in result.stdout.splitlines()]
            assert len(depths)==len(reps) and all(1<=d<=m for d in depths)
            print('mixed',m,'lines',L,'cases',case_count,'representatives',len(reps),'extinction',sorted(Counter(depths).items()),flush=True)
        for m in ([args.mixed] if args.mixed else range(18,22)):
            for L in ([args.lines] if args.lines else (7,8,9)):
                replay(m,L)

if __name__=='__main__':
    main()
