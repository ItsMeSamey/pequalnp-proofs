from itertools import combinations
from pathlib import Path
import sys
from pysat.card import CardEnc,EncType
from pysat.formula import IDPool
from pysat.solvers import Cadical195

def jobs(base):
 result=set()
 for path in base.glob('p6-*.live'):
  common=int(path.stem[-1])
  for line in path.read_text().splitlines():
   _,p,q,*tag=map(int,line.split())
   tup=tuple(sorted((u,((p>>i)&1)|((((p if common else q)>>i)&1)<<1)) for i,u in enumerate(tag)))
   result.add((common,tup))
 return sorted(result)

def solve(common,rows):
 V=IDPool();sat=Cadical195()
 def new():return V.id()
 def conjunction(a,b):
  z=new();sat.add_clause([-z,a]);sat.add_clause([-z,b]);sat.add_clause([z,-a,-b]);return z
 def disjunction(a,b):return -conjunction(-a,-b)
 def limit(xs,lo=None,hi=None):
  if lo is not None and lo>0:sat.append_formula(CardEnc.atleast(lits=xs,bound=lo,vpool=V,encoding=EncType.seqcounter).clauses)
  if hi is not None and hi<len(xs):sat.append_formula(CardEnc.atmost(lits=xs,bound=hi,vpool=V,encoding=EncType.seqcounter).clauses)
 def pack(values):return sum((v<<i) for i,v in enumerate(values))
 n=len(rows);D=5;U=[t>>4 for t,_ in rows];B=[t&15 for t,_ in rows];P=[v for _,v in rows]
 known_pos=[u&~p for u,p in zip(U,P)];known_neg=[p&~u for u,p in zip(U,P)];known_hot=[u&p for u,p in zip(U,P)]
 hot=sum(any(k>>j&1 for k in known_hot) for j in range(2))
 ext=[b|(h<<4) for b,h in zip(B,known_hot)]
 pure=[b.bit_count()+u.bit_count()==2 for b,u in zip(B,U)]
 pure_size=sum(b.bit_count()+u.bit_count() for b,u in zip(B,U))
 hmin=max(0,2+(max(0,8+hot-(26-pure_size))+1)//2-hot)
 caps=[2+b.bit_count()+common+(bool(p) if common else p.bit_count())-(p|u).bit_count() for b,p,u in zip(B,P,U)]
 pos=[];neg=[];used=[];rank=[]
 for j in range(D):
  a=[new() for _ in rows];b=[new() for _ in rows]
  for i in range(n):
   if pure[i]:
    for k in range(n):
     if i!=k and not ext[i]&~ext[k]:sat.add_clause([-a[i],a[k]]);sat.add_clause([-b[i],b[k]])
  yes=[conjunction(x,-y) for x,y in zip(a,b)];no=[conjunction(-x,y) for x,y in zip(a,b)]
  for i in range(n):sat.add_clause([-no[i],*yes[:i]])
  limit(yes,lo=3);limit(no,lo=3)
  hs=[conjunction(x,y) for x,y in zip(a,b)]
  mark=new();sat.add_clause([-mark,*hs])
  for h in hs:sat.add_clause([mark,-h])
  if j<hmin:sat.add_clause([mark])
  rank.append([-mark]+[v for pair in zip(yes,no) for v in pair])
  pos.append(yes);neg.append(no);used.append([disjunction(x,y) for x,y in zip(a,b)])
 for left,right in zip(rank,rank[1:]):
  equal=None
  for a,b in zip(left,right):
   gate=[] if equal is None else [-equal]
   sat.add_clause(gate+[-a,b])
   same=disjunction(conjunction(a,b),conjunction(-a,-b))
   equal=same if equal is None else conjunction(equal,same)
 fields=[[i for i in range(n) if (known_pos[i]&f)==known_pos[i] and not known_neg[i]&f] for f in range(4)]
 vol=[1<<(D-min(D,c)) for c in caps]
 for i in range(n):
  limit([u[i] for u in used],hi=caps[i])
  mn=0
  for group in fields:
   if i in group:
    rem=(1<<D)-sum(vol[j] for j in group if j!=i)
    if rem<=0:return False
    mn=max(mn,D-(rem.bit_length()-1))
  if mn>0:limit([u[i] for u in pos+neg],lo=mn)
 for word in range(1<<D):
  matches=[]
  for i in range(n):
   bad=[neg[j][i] if word>>j&1 else pos[j][i] for j in range(D)]
   match=new();sat.add_clause([match,*bad])
   for v in bad:sat.add_clause([-match,-v])
   matches.append(match)
  for group in fields:limit([matches[i] for i in group],hi=1)
 for i,k in combinations(range(n),2):
  if (known_pos[i]&known_neg[k]) or (known_pos[k]&known_neg[i]):continue
  sat.add_clause([conjunction(sign[j][i],op[j][k]) for j in range(D) for sign,op in [(pos,neg),(neg,pos)]])
 sat.conf_budget(15000)
 result=sat.solve_limited();sat.delete();return result
if __name__=='__main__':
 base=Path(sys.argv[1]);task=jobs(base);print('profiles',len(task),file=sys.stderr,flush=True)
 lo,hi=map(int,sys.argv[2:4])
 for k in range(lo,min(hi,len(task))):
  c,raw=task[k];print(k,solve(c,raw),flush=True)
