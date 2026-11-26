from pathlib import Path
from itertools import combinations
import hashlib,re,sys
src=Path(__file__).parent/'sealed'
sys.path.insert(0,str(src))
from high_local import geom, compulsory, inc, unique, meeting, N
bits=[1<<i for i in range(13) if compulsory&(1<<i)]
def domain(t):
    prev={0}; kept=set()
    for length in range(1,len(bits)+1):
        curr=set()
        for group in combinations(bits,length):
            m=sum(group)
            if any(m-b not in prev for b in group):continue
            n=0
            for p,u in inc:
                if m&(1<<p):n|=unique[p,u]
            while True:
                room=[2+(u==t)-v for u,v in enumerate(geom(m,n))]
                if min(room)<0:break
                full={u for u,v in enumerate(room) if not v}
                nn=n
                for u in full:nn|=meeting[u]
                if nn!=n:n=nn;continue
                curr.add(m)
                if all(not(n&unique[p,u]) for p,u in inc if u in full and compulsory&(1<<p) and not m&(1<<p)):kept.add(m)
                break
        prev=curr
        if not curr:break
    return kept
def expand(t,ms):
    out=[]
    for m in sorted(ms,key=lambda x:(-x.bit_count(),x)):
        forbidden=0
        for p,u in inc:
            if not m&(1<<p):continue
            flags=unique[p,u]
            while flags:
                bit=flags&-flags;flags-=bit;forbidden|=N[bit.bit_length()-1]
        out.append((t,m,0))
        out.extend((t,m,b) for b in bits if m&b and not forbidden&b)
    return out
def ledger():
    res=[{} for _ in range(7)]
    for path in [src/'high-t0-case0.log',src/'high-t0-offset1-12.log',*sorted((src/'high-checkpoints').glob('*.log'))]:
        rows=[];checks=[]
        for line in path.read_text().splitlines():
            if line.startswith('CASE '):
                match=re.fullmatch(r'CASE (\d+) (\d+) (\d+) 0 \[\]',line)
                assert match,(path,line)
                rows.append(tuple(map(int,match.groups())))
            elif line.startswith('CHECKPOINT '):checks.append(tuple(map(int,line.split()[1:])))
        if not rows:continue
        t=rows[0][0]; name=path.name
        start=0 if name=='high-t0-case0.log' else 1 if name=='high-t0-offset1-12.log' else int(re.fullmatch(r't\d+-at(\d+)\.log',name)[1])
        for t1,off,n,total in checks:assert (t1,off,n)==(t,start,len(rows))
        for i,r in enumerate(rows,start):
            assert i not in res[t] and r[0]==t,(path,i)
            res[t][i]=r
    return res
if __name__=='__main__':
    allrows=ledger()
    for t,data in enumerate(allrows):
        masks={m for _,m,_ in data.values()} if '--ledger' in sys.argv else domain(t)
        expected=expand(t,masks)
        assert dict(enumerate(expected))==data,t
        print(t,len(masks),len(expected),hashlib.sha256(repr(expected).encode()).hexdigest(),flush=True)
