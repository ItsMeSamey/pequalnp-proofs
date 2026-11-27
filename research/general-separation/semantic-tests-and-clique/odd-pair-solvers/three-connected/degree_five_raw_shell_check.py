"""Exact shell audit. Keep actual partial vertex masks, count only when making a dedup key."""
from itertools import combinations
from collections import Counter
from pathlib import Path
import json


def ones(mask):
    while mask:
        b=mask&-mask
        yield b.bit_length()-1
        mask^=b


def expand(mask,sites):
    return sum(1<<sites[i] for i in ones(mask))


def pack(mask,sites):
    return sum((mask>>i&1)<<j for j,i in enumerate(sites))


class Raw:
    def __init__(self,rows,ports,words):
        self.rows=tuple(rows)
        self.ports=tuple(ports)
        self.degrees=tuple(rows[i].bit_count() for i in ports)
        self.words=[]
        size=1<<len(ports)
        counts=[[0]*size for _ in range(size)]
        self.ok=[[] for _ in range(size)]
        allowed=expand(size-1,ports)
        for w in words:
            defect=sum(1<<v for v in ones(w) if (rows[v]&w).bit_count()%2==0)
            if defect&~allowed:
                continue
            self.words.append(w)
            u=pack(w,ports)
            e=pack(defect,ports)
            for v in range(size):
                if u&v==e:
                    self.ok[v].append((w,u))
                    counts[v][u]=min(2,counts[v][u]+1)
        self.key=self.degrees,tuple(tuple(row) for row in counts)


def grow(old):
    n=len(old.rows)
    ports=old.ports
    maxdeg=tuple(5-d for d in old.degrees)
    k=len(ports)
    memberships=[]
    inside=[]
    # Pre-screen contact multisets independently of the new internal edges.
    # All new sites selected already fixes the drift on the old boundary.
    # If another actual old word gives identical parity at every new row,
    # it extends to the same exterior and precludes a minimal host.
    good_prefix=set()
    rowtypes=[t for t in range(1,1<<k) if not any((t&u).bit_count()%2 for w,u in old.ok[t])]
    def list_contacts(prefix,used,index,drift):
        if len(prefix)>=3 and sum(v>0 for v in used)>=3 and all(
                d+v in (3,5) for d,v in zip(old.degrees,used)):
            alternatives=[w for w,u in old.ok[drift]
                          if all(((~u)&t).bit_count()%2==0 for t in prefix)]
            if alternatives==[(1<<n)-1]:
                for j in range(1,len(prefix)+1):
                    good_prefix.add(prefix[:j])
        for j in range(index,len(rowtypes)):
            t=rowtypes[j]
            add=tuple(v+(t>>i&1) for i,v in enumerate(used))
            if all(x<=y for x,y in zip(add,maxdeg)):
                list_contacts(prefix+(t,),add,j,drift^t)
    list_contacts((),(0,)*k,0,0)
    def walk(last,used,choices):
        m=len(memberships)
        if m>=3 and sum(v>0 for v in used)>=3 and all(d+v in (3,5) for d,v in zip(old.degrees,used)):
            ds=[t.bit_count()+r.bit_count() for t,r in zip(memberships,inside)]
            nextports=tuple(n+i for i,d in enumerate(ds) if d<5)
            if len(nextports)>=3:
                rr=list(old.rows)+[expand(t,ports)|(r<<n) for t,r in zip(memberships,inside)]
                for i,t in enumerate(memberships):
                    for j in ones(t):
                        rr[ports[j]]|=1<<(n+i)
                # Actual old words must satisfy every old guard once new sites are fixed.
                words=(w|(s<<n) for s,v in choices for w,u in old.ok[v])
                new=Raw(rr,nextports,words)
                fully=(1<<len(rr))-1
                incoming=sum((1^(d%2))<<i for i,d in enumerate(new.degrees))
                fullport=(1<<len(nextports))-1
                if not new.ok[0] and [w for w,u in new.ok[incoming] if u==fullport]==[fully]:
                    yield new
        for t in range(last,1<<k):
            if tuple(memberships)+(t,) not in good_prefix:continue
            add=tuple(v+(t>>i&1) for i,v in enumerate(used))
            if any(x>y for x,y in zip(add,maxdeg)):
                continue
            # A witness confined to one new vertex remains under any completion.
            if any((t&u).bit_count()%2 for w,u in old.ok[t]):
                continue
            ready=[(s|(1<<m),v^t) for s,v in choices]
            for adj in range(1<<m):
                if t.bit_count()+adj.bit_count()>5 or any(
                    memberships[j].bit_count()+inside[j].bit_count()>=5 for j in ones(adj)):
                    continue
                # Check every word selecting the newest vertex and any subset of its
                # predecessors in this layer, with all subsequent vertices vacant.
                local_found=False
                for ns,v in ready:
                    for w,u in old.ok[v]:
                        if ((u&t).bit_count()+(ns&adj).bit_count())%2==0:
                            continue
                        if all(((u&memberships[j]).bit_count()+(ns&inside[j]).bit_count()
                                +(adj>>j&1))%2 for j in ones(ns^(1<<m))):
                            local_found=True
                            break
                    if local_found: break
                if local_found:
                    continue
                memberships.append(t)
                for j in ones(adj):inside[j]|=1<<m
                inside.append(adj)
                yield from walk(t,add,choices+ready)
                inside.pop()
                for j in ones(adj):inside[j]^=1<<m
                memberships.pop()
    yield from walk(1,(0,)*k,[(0,0)])


def main():
    src=Path(__file__).with_name('degree_five_common_core_census.json')
    initial={}
    for group in json.loads(src.read_text()):
        for d in group['orbits']:
            if d['all_pieces_reach_port']:
                rr=d['rows']
                ports=[i for i,v in enumerate(d['exterior_degrees'],2) if max(v)>0]
                st=Raw(rr,ports,range(3,1<<len(rr),4))
                initial[st.key]=st
    states=initial
    print('initial',len(states),flush=True)
    for depth in range(1,5):
        nxt={}
        edges=Counter()
        for old in states.values():
            for new in grow(old):
                nxt[new.key]=new
                edges[len(new.ports)]+=1
        print(depth,len(nxt),edges,flush=True)
        states=nxt
    assert not states


if __name__=='__main__':
    main()
