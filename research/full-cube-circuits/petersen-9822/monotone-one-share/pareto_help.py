from pathlib import Path
from graph import E,Z
import json
EM=8191;NM=65535<<13
def bits29(m):
 while m:
  x=m&-m;yield x.bit_length()-1;m^=x
def nondominated(pool):
 idx=[0]*29;out={}
 for k in sorted(pool,key=int.bit_count,reverse=True):
  bs=list(bits29(k));v=idx[bs[0]]
  for i in bs[1:]:
   if not v:break
   v&=idx[i]
  if v:continue
  flag=1<<len(out);out[k]=pool[k]
  for i in bs:idx[i]|=flag
 return out
def main():
 front=[None,{}]
 for i in range(10):
  b=1<<i;k=sum(1<<j for j,e in enumerate(E) if e&b)|sum(1<<(13+j) for j,z in enumerate(Z) if not z&b)
  front[1][k]=(b,1,str(i))
 for n in range(2,8):
  pool=front[n-1].copy()
  for a in range(1,n//2+1):
   for x,(sx,ax,px) in front[a].items():
    for y,(sy,ay,py) in front[n-a].items():
     if 2*a==n and x>y:continue
     for k,z,op in ((EM&(x|y)|NM&x&y,sx|sy,'|'),(EM&x&y|NM&(x|y),sx&sy,'&')):
      if not k&EM or not k&NM:continue
      old=pool.get(k)
      if old is None or ax+ay<old[1] or (ax+ay==old[1] and z and not old[0]):
       pool[k]=(z,ax+ay,f'({px}{op}{py})')
  front.append(nondominated(pool));print(n,len(pool),len(front[n]),flush=True)
  Path(f'pareto-{n}.json').write_text(json.dumps(front[n],separators=(',',':')))
if __name__=='__main__':main()
