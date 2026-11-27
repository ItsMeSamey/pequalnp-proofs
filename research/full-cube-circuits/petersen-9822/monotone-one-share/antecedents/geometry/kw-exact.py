import itertools,numpy as np
from scipy.sparse import coo_matrix
from scipy.optimize import linprog
E=[(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
Z=[s for s in range(1024) if all(not(s>>v&s>>w&1) for v,w in E)]
Z=[s for s in Z if all((s|1<<k) not in Z for k in range(10) if not s>>k&1)]
nvar=len(E)*len(Z);V=nvar;R=[];C=[];D=[];B=[]
def inequality(v,t):
 row=len(B);B.append(t)
 for i,a in v:R.append(row);C.append(i);D.append(a)
for x in range(10):
 H=[i for i,e in enumerate(E) if x in e]
 I=[i for i,s in enumerate(Z) if not s>>x&1]
 for n in range(1,len(H)+1):
  for J in itertools.combinations(H,n):
   sl=[]
   for i in I:
    sl.append(V);inequality([(j*len(Z)+i,1) for j in J]+[(V,-1)],0);V+=1
   inequality([(v,1) for v in sl],1)
A=coo_matrix((D,(R,C)),shape=(len(B),V)).tocsr(); obj=np.zeros(V);obj[:nvar]=-1
op=linprog(obj,A_ub=A,b_ub=B,bounds=[(None,None)]*nvar+[(0,None)]*(V-nvar),method='highs-ds', options={'threads':1,'time_limit':17})
print('vertices',len(Z),'status',op.message,'weight',(-op.fun if op.success else None),flush=True)

if op.success:
 from fractions import Fraction as F
 import json
 q=lambda x:F(float(x)).limit_denominator(100000)
 w=list(map(q,op.x[:nvar]))
 worst=max(sum(max(sum(w[e*len(Z)+j] for e in J),0) for j,b in enumerate(Z) if not(b>>v&1)) for v in range(10) for k in range(1,4) for J in itertools.combinations([i for i,e in enumerate(E) if v in e],k))
 assert worst<=1
 y=list(map(lambda x:q(-x),op.ineqlin.marginals))
 assert min(y)>=0
 dual=[F(0)]*V
 for a,r,c in zip(D,R,C):dual[c]+=int(a)*y[r]
 assert dual[:nvar]==[1]*nvar and min(dual[nvar:])>=0
 assert sum(x*int(b) for x,b in zip(y,B))==sum(w)
 print('exact',sum(w),'worst',worst,flush=True)
 open('kw-exact.json','w').write(json.dumps({'w':list(map(str,w)),'dual':list(map(str,y))}))
