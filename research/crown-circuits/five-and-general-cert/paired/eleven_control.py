from pathlib import Path
import json
g=json.loads(Path('fourbit-flat41.json').read_text())
def control(drop):
 n=11;P=(1<<n);raw=[sum(1<<p for p in range(P) if p>>i&1) for i in range(n)];target=sum(1<<p for p in range(P) if p.bit_count()>=2)
 wires=[];nodes=[];idx={v:i for i,v in enumerate(raw)}
 labels=[0 if i==drop else raw[i-(i>drop)] for i in range(12)]
 vals=labels*2
 for op,a,b in g['gates']:
  x,y=vals[a],vals[b];v=(x|y) if op=='or' else (x&y);vals.append(v)
  if v==0 or v in idx:continue
  idx[v]=n+len(nodes);nodes.append((op,idx[x],idx[y]))
 root=idx[vals[g.get('output',len(vals)-1)]]
 assert vals[g.get('output',len(vals)-1)]==target
 live=set()
 def visit(j):
  if j>=n and j not in live:
   live.add(j);_,a,b=nodes[j-n];visit(a);visit(b)
 visit(root);m={i:i for i in range(n)};final=[]
 for i in sorted(live):
  o,a,b=nodes[i-n];m[i]=n+len(final);final.append([o,m[a],m[b]])
 return dict(n=n,size=len(final),ands=sum(x[0]=='and' for x in final),output=m[root],dropped=drop,gates=final)
D=min([control(i) for i in range(12)],key=lambda d:d['size'])
print(D['n'],D['size'],D['ands'],D['dropped'])
Path('eleven-control.json').write_text(json.dumps(D)+'\n')
