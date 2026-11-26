"""Exhaust interval parse and elimination widths of restricted-growth words."""
from functools import cache
import sys


def parse_width(word):
    n=len(word)
    pref=[]; suff=[0]*(n+1); a=0
    for v in word:
        pref.append(a)
        a|=1<<v
    for i in range(n-1,-1,-1):
        suff[i]=suff[i+1]|1<<word[i]
    dp={}
    for i in range(n-1,-1,-1):
        inside=0
        for j in range(i+1,n+1):
            inside |= 1<<word[j-1]
            boundary=(inside & (pref[i]|suff[j])).bit_count()
            child=min((max(dp[i,k],dp[k,j]) for k in range(i+1,j)),default=0)
            dp[i,j]=max(boundary,child)
    return dp[0,n]


def join_width(word):
    n=len(word)
    pre=[0]*(n+1)
    suf=[0]*(n+1)
    for i in range(n):
        pre[i+1]=pre[i]|1<<word[i]
        suf[n-1-i]=suf[n-i]|1<<word[n-1-i]
    dp={}
    bs={}
    for i in range(n-1,-1,-1):
        seen=0
        for j in range(i+1,n+1):
            seen |= 1<<word[j-1]
            bs[i,j]=seen&(pre[i]|suf[j])
            dp[i,j]=min((max(dp[i,k],dp[k,j],(bs[i,k]|bs[k,j]).bit_count())
                         for k in range(i+1,j)),default=1)
    return dp[0,n]


def alt_edges(word):
    # A pair alternates iff its projection has at least four nonempty runs.
    r=max(word)+1
    g=[0]*r
    for b in range(r):
        for a in range(b):
            seq=[v for v in word if v==a or v==b]
            if sum(u!=v for u,v in zip(seq,seq[1:]))>=3:
                g[a]|=1<<b
                g[b]|=1<<a
    return tuple(g)


@cache
def tw(graph):
    if not graph:
        return -1
    low=min(v.bit_count() for v in graph)
    best=len(graph)-1
    for v,neighbors in enumerate(graph):
        degree=neighbors.bit_count()
        if degree>=best:
            continue
        rem=[]
        for u,adj in enumerate(graph):
            if u==v:
                continue
            if neighbors>>u&1:
                adj=(adj|neighbors)&~(1<<u)
            rem.append((adj&((1<<v)-1))|((adj>>(v+1))<<v))
        best=min(best,max(degree,tw(tuple(rem))))
        if best==low:
            break
    return best


def words(prefix,n):
    if len(prefix)==n:
        yield prefix
    else:
        for v in range(max(prefix)+2):
            yield from words(prefix+(v,),n)


if __name__=='__main__':
    for n in range(1,int(sys.argv[1]) + 1 if len(sys.argv)>1 else 11):
        count=0
        tight=0
        for w in words((0,),n):
            t=tw(alt_edges(w))
            width=parse_width(w)
            if join_width(w)!=t+1 or width>t+1:
                raise AssertionError((w,width,t))
            tight+=width==t+1
            count+=1
        print(n,count,tight,flush=True)
