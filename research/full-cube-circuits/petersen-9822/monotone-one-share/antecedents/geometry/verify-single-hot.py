exec(open('verify-extended.py').read().split('for w,d in list')[0])
bank=list(db.values())+list(fresh.values());src={}
for c,s,a,b,r,q,ws in lines('kw-hot.jsonl')+lines('kw-hot-extra.jsonl')+lines('kw-hot-last.jsonl'):
 src[c,s,a,b,r,q]=weight(ws)
perm=(3,2,1,0,4,8,7,6,5,9)
def flip(s):return sum(1<<v for i,v in enumerate(perm) if s>>i&1)
more=[]
for *_,ws in lines('kw-hot.jsonl'):
 W,d=weight(ws);more.extend([(W,d),([W[16*E.index(flip(e))+Z.index(flip(z))] for e in E for z in Z],d)])
for row in map(str.split,open('hot-reuse-next.log')):
 *key,i=map(int,row)
 if i>=0:src[tuple(key)]=more[i]
def allowed(c,s,a,b,r,q):
 if c==5:
  if a&b or (a|b).bit_count()!=5 or (a|b)>>s&1:return False
  T=[e for e in E if e&(a|b)==e and e&a and e&b]
  if len(T)!=4 or any(not any(e>>v&1 for e in T) for v in range(10) if (a|b)>>v&1):return False
  return True
 return c==6 and s==9 and b==0 and a.bit_count()==6 and not a>>9&1
universe=set()
for s in range(10):
 for a in range(1,1024):
  if a>>s&1:continue
  for b in range(a+1,1024):
   if allowed(5,s,a,b,0,0):
    H=lambda z:z>>s&1 or (z&a and z&b)
    universe.add((5,s,a,b,sum(1<<i for i,e in enumerate(E) if H(e)),sum(1<<i for i,z in enumerate(Z) if not H(z))))
for a in range(512):
 if a.bit_count()==6:universe.add((6,9,a,0,sum(1<<i for i,e in enumerate(E) if e>>9&1 or e&a==e),sum(1<<i for i,z in enumerate(Z) if not z>>9&1)))
rows={tuple(map(int,l.split()[:6])):int(l.split()[6]) for l in open('hot-reuse.log')}
assert set(rows)==universe
done={};fails=[]
for key,id in rows.items():
 if id<0 and key not in src:fails.append(key);continue
 W,d=bank[id] if id>=0 else src[key];rawcheck(W,d)
 c,s,a,b,r,q=key
 MX=max(d,price([i for i in range(13) if r>>i&1],[i for i in range(16) if q>>i&1],W))
 if sum(W)<=(18-c)*MX:fails.append(key);continue
 done[c]=done.get(c,0)+1
print(done,'unresolved',len(fails),fails)
