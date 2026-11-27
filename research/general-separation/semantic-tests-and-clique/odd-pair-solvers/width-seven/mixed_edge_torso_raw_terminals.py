"""Mixed-parity endpoint census, all physical histories and full native subset checks."""
from itertools import combinations,product
from collections import Counter
from degree_five_raw_shell_check import Raw, expand, ones, pack
from degree_five_raw_terminal_check import tri
from degree_five_active_shells import root, grow, glue, key
from mixed_edge_torso_shells import roots


def native(looped):
    # Strip the auxiliary loop; explicitly enforce even at pin zero.
    rows=[looped[0]^1,*looped[1:]]
    full=(1<<len(rows))-1
    if not tri(rows) or any((r.bit_count()%2)!=(i!=0) for i,r in enumerate(rows)):
        return False
    return not any(all((rows[i]&s).bit_count()%2==(i!=0) for i in ones(s)) for s in range(3,full,4))


def terminal(old):
    n=len(old.rows);k=len(old.ports);oldfull=(1<<n)-1
    opts=[tuple(f-d for f in (3,5) if f>=d) for d in old.degrees]
    alltypes=list(range(1,1<<k))
    single={}
    for t in alltypes:
        single[t]=[w for w,u in old.ok[t] if (u&t).bit_count()%2]
    def rowsets(ds,lo,prefix):
        if not any(ds):
            if (len(prefix)+n)%2==1:yield prefix
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
                            assert native(rr)
                            yield tuple(rr)
                        return
                    i,j=free[pos]
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                    yield from attach(pos+1)
                    rr[i]^=1<<j;rr[j]^=1<<i
                yield from attach(0)


def templates(raw):
    n=len(raw.rows)
    return [(tuple(pack(row,raw.ports) for row in rr[n:]),tuple(row>>n for row in rr[n:]))
            for rr in terminal(raw)]


def main():
    queue=list(roots())
    # Keep all physical histories. The nonterminal incidence proposals depend only
    # on the capped table, but endpoints and connectivity are checked on each graph.
    examples={}
    aggregate=Counter()
    depth=0
    while queue:
        later=[]
        counts=Counter()
        cache={}
        for r in queue:
            rows,ports=r.rows,r.ports
            d,packed=r.key
            t=[{u:c for u,c in enumerate(row) if c} for row in packed]
            for inc,ext in templates(r):
                graph,_=glue(rows,ports,inc,ext)
                assert native(graph)
                counts[len(graph)]+=1
                examples.setdefault(len(graph),(graph[0]^1,*graph[1:]))
            token=key(d,t)
            if token not in cache:
                cache[token]=[(inc,ext) for _,_,inc,ext in grow(d,t)]
            for inc,ext in cache[token]:
                graph,new_ports=glue(rows,ports,inc,ext)
                sig=[0]*(1<<len(inc))
                for mask in range(1,len(sig)):
                    bit=mask&-mask
                    sig[mask]=sig[mask^bit]^inc[bit.bit_length()-1]
                # Once the new selection is fixed, all old constraints have a
                # fixed incoming parity. This enumerates every possible prefix mask.
                words=(w|(mask<<len(rows)) for mask,v in enumerate(sig) for w,u in r.ok[v])
                later.append(Raw(graph,new_ports,words))
        aggregate.update(counts)
        print(depth,len(queue),sorted(counts.items()),len(later),flush=True)
        depth+=1
        queue=later
    print('total',sorted(aggregate.items()),'examples',examples,flush=True)


if __name__=='__main__':
    main()
