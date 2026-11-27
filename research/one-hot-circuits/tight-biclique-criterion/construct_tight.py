"""Build d-1 gates for a matrix whose nonuniversal residual is a biclique union."""
import json,re,sys
from rank import classify

def build(rows,m):
    n=len(rows); allcols=(1<<m)-1
    universalc=[j for j in range(m) if all(r>>j&1 for r in rows)]
    universalm=sum(1<<j for j in universalc)
    groups={}
    for i,r in enumerate(rows):
        c=r & ~universalm
        if c and r!=allcols:groups.setdefault(c,[]).append(i)
    if any(c!=e and c&e for c in groups for e in groups):return None
    gates=[]
    def combine(op,ws):
        start,*rest=ws
        for w in rest:
            gates.append([op,start,w]);start=n+m+len(gates)-1
        return start
    terms=[i for i,r in enumerate(rows) if r==allcols]+[n+j for j in universalc]
    for c,rs in groups.items():
        p=combine('or',rs); q=combine('or',[n+j for j in range(m) if c>>j&1])
        terms.append(combine('and',[p,q]))
    if not terms:return None
    out=combine('or',terms)
    for i in range(n):
        for j in range(m):
            w=[v in (i,n+j) for v in range(n+m)]
            for op,x,y in gates:w.append((w[x] and w[y]) if op=='and' else (w[x] or w[y]))
            if w[out]!=bool(rows[i]>>j&1):raise ValueError((i,j))
    return gates,out
if __name__=='__main__':
    data=json.load(open(sys.argv[1]))
    offers=[(r['id'],r['title']) for r in data['gaps'] if r['offerable'] and ('side promise' in r['title'] or 'Table 1a' in r['title'])] if data['gaps'] and isinstance(data['gaps'][0],dict) else data['gaps']
    print('snapshot',data.get('updated_at'),'offers',len(offers))
    for rid,title in offers:
        n,m=map(int,re.search(r'(\d+) by (\d+)',title).groups());d=classify(title)
        rows=[d['mask']>>(m*i)&((1<<m)-1) for i in range(n)]
        wit=build(rows,m)
        if wit is not None:
            assert len(wit[0])==d['charged']-1
            if len(wit[0])<=d['cap']:print('MATCH',rid,json.dumps(wit))
