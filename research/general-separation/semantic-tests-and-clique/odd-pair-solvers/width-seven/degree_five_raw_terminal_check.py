"""Physical terminal census, without deduplicating intermediate shell states."""
from collections import Counter
from itertools import combinations,product
from pathlib import Path
import json
from degree_five_raw_shell_check import Raw,grow,expand,ones


def tri(rows):
    n=len(rows)
    if n<4 or min(v.bit_count() for v in rows)<3:return False
    full=(1<<n)-1
    for i,j in combinations(range(n),2):
        live=full^(1<<i)^(1<<j)
        seen=live&-live
        todo=seen
        while todo:
            fresh=0
            for v in ones(todo):fresh|=rows[v]
            todo=fresh&live&~seen
            seen|=todo
        if seen!=live:return False
    return True


def minimal(rows):
    full=(1<<len(rows))-1
    if any(v.bit_count()%2==0 for v in rows):return False
    return not any(all((rows[i]&s).bit_count()%2 for i in ones(s))
                   for s in range(3,full,4) if s.bit_count()%2==0)


def bare():
    counts=Counter()
    for c in range(1,6):
        sizes=[d-c for d in (3,5) if d>=c]
        for a,b in ((a,b) for a in sizes for b in sizes if a<=b):
            A=list(range(2,2+a));B=list(range(2+a,2+a+b));C=list(range(2+a+b,2+a+b+c))
            n=2+a+b+c
            if n%2:continue
            rows=[0]*n
            def toggle(i,j):
                rows[i]^=1<<j
                rows[j]^=1<<i
            for i in A+C:toggle(0,i)
            for i in B+C:toggle(1,i)
            for i,j in product(A,B):toggle(i,j)
            slots=[(i,j) for i,j in combinations(range(2,n),2) if not rows[i]>>j&1]
            def visit(pos):
                if pos==len(slots):
                    if tri(rows) and minimal(rows):
                        counts[n]+=1
                    return
                i,j=slots[pos]
                visit(pos+1)
                if max(rows[i].bit_count(),rows[j].bit_count())<5:
                    toggle(i,j)
                    visit(pos+1)
                    toggle(i,j)
            visit(0)
    return counts


def terminal(old):
    n=len(old.rows);k=len(old.ports);oldfull=(1<<n)-1
    opts=[tuple(f-d for f in (3,5) if f>=d) for d in old.degrees]
    alltypes=list(range(1,1<<k))
    single={}
    for t in alltypes:
        single[t]=[w for w,u in old.ok[t] if (u&t).bit_count()%2]
    def rowsets(ds,lo,prefix):
        if not any(ds):
            if (len(prefix)+n)%2==0:yield prefix
            return
        for t in range(lo,1<<k):
            residual=tuple(d-(t>>i&1) for i,d in enumerate(ds))
            if min(residual)<0:continue
            if (prefix or any(residual)) and single[t]:continue
            yield from rowsets(residual,t,prefix+(t,))
    for ds in product(*opts):
        if sum(d>0 for d in ds)<3:continue
        for ts in rowsets(ds,1,()):
            m=len(ts)
            if m>1 and any(single[t] for t in ts):continue
            # With every new vertex selected, preserving each new-site incoming bit
            # must force the full old word; independent of all new internal edges.
            sigma=0
            for t in ts:sigma^=t
            if [w for w,u in old.ok[sigma]
                if all(((~u)&t).bit_count()%2==0 for t in ts)]!=[oldfull]:continue
            rr=list(old.rows)+[expand(t,old.ports) for t in ts]
            for i,t in enumerate(ts):
                for b in ones(t):rr[old.ports[b]]|=1<<(n+i)
            free=[]
            for i,j in combinations(range(m),2):
                opts2=[0,1]
                if m>2:
                    for bit in (0,1):
                        if any((bit+(u&ts[i]).bit_count())%2 and (bit+(u&ts[j]).bit_count())%2
                               for w,u in old.ok[ts[i]^ts[j]]):
                            opts2.remove(bit)
                if not opts2:break
                if opts2==[1]:
                    rr[n+i]|=1<<(n+j);rr[n+j]|=1<<(n+i)
                if len(opts2)==2:free.append((n+i,n+j))
            else:
                def attach(pos):
                    if any(v.bit_count()>5 for v in rr[n:]):return
                    if pos==len(free):
                        if all(v.bit_count() in (3,5) for v in rr[n:]) and tri(rr):
                            # Enumerate all native words by new-layer subset and actual
                            # old words. Unlike an unstructured power-set scan, this
                            # also remains cheap on the longer losing extensions.
                            for s in range(1<<m):
                                drift=0
                                for j in ones(s):drift^=ts[j]
                                for w,u in old.ok[drift]:
                                    raw=w|(s<<n)
                                    if raw!=(1<<len(rr))-1 and all((rr[n+j]&raw).bit_count()%2 for j in ones(s)):return
                            assert minimal(rr)
                            yield tuple(rr)
                        return
                    i,j=free[pos]
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                yield from attach(0)


def main():
    data=json.loads(Path(__file__).with_name('degree_five_common_core_census.json').read_text())
    root=[]
    for cell in data:
        for rec in cell['orbits']:
            if rec['all_pieces_reach_port']:
                rr=rec['rows']
                root.append(Raw(rr,[i for i,v in enumerate(rec['exterior_degrees'],2) if max(v)>0],
                                range(3,1<<len(rr),4)))
    print('bare labelled',bare(),flush=True)
    for depth in range(1,5):
        results=Counter()
        sample={}
        later=[]
        for s in root:
            for rr in terminal(s):
                results[len(rr)]+=1
                sample[len(rr)]=rr
            later.extend(grow(s))
        print(depth,'incoming',len(root),'terminals',results,'next',len(later),'examples',sample,flush=True)
        root=later
    assert not root


if __name__=='__main__':
    main()
