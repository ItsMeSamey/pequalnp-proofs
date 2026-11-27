exec(open('verify-helper-weights.py').read().split('boundary=[]')[0])
src={tuple(s):[F(x) for x in w] for s,w in map(json.loads,Path('kw-or4.jsonl').read_text().splitlines())}
reuse=json.loads(Path('reuse-or4.json').read_text())
def price(m,w):
 rows=[i for i,e in enumerate(E) if e&m];cols=[j for j,z in enumerate(Z) if not z&m]
 x=[(0,)*len(rows)];best=F(0)
 for j in cols:
  n=[tuple(v+w[16*i+j] for v,i in zip(s,rows)) for s in x];x+=n
  best=max(best,max(sum(max(0,y) for y in v) for v in n))
 return max(1,best)
for s in itertools.combinations(range(10),4):
 m=sum(1<<v for v in s)
 if str(m) in reuse:w=db[tuple(reuse[str(m)])]
 else:
  w=src[s];assert all(price(1<<v,w)==1 for v in range(10))
 assert sum(w)>15*price(m,w)
print('210 four-raw OR labels excluded')
