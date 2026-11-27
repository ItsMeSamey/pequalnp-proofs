from pathlib import Path
import json
base=json.loads((Path(__file__).parent/'input18.json').read_text())
fan={i:sum(g[1:].count(i) for g in base) for i in range(10+len(base))}
def make(gi,operand):
 g=[];old={i:i for i in range(10)}
 def op(k,a,b):g.append([k,a,b]);return len(g)+9
 for i,(k,a,b) in enumerate(base,10):
  if i==operand:continue
  if i==gi:
   p,q=base[operand-10][1:];r=b if operand==a else a
   old[i]=op('or',op('and',old[p],old[r]),op('and',old[q],old[r]))
  else:old[i]=op(k,old[a],old[b])
 return g
for i,(op,a,b) in enumerate(base,10):
 if op=='and':
  for s in (a,b):
   if s>=10 and fan[s]==1 and base[s-10][0]=='or':break
  else:continue
  g=make(i,s);break
E=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
for x in range(1024):
 w=[bool(x>>i&1) for i in range(10)]
 for op,a,b in g:w.append(w[a] and w[b] if op=='and' else w[a] or w[b])
 assert w[-1]==any((x>>i&1) and (x>>j&1) for i,j in E)
assert len(g)==19 and sum(k=='and' for k,a,b in g)==7
Path('upper19-seven.json').write_text(json.dumps(g)+'\n')
print('19 gates, 7 AND, 1024/1024')
