from g3_den_hadamard import *
def filterC(r,S,y):
 X=[sum((int(s[i])<0)<<(i-1) for i in range(1,r)) for s in S]
 t=sum((int(v)<0)<<j for j,v in enumerate(y))
 n=len(X); allbits=(1<<n)-1
 cols={sum(((x&b).bit_count()%2)<<j for j,x in enumerate(X)) for b in range(1<<(r-1))}
 return any((w&(t^c))==0 or (w&(~(t^c)))==0 for a in {sum(((x&b).bit_count()%2)<<j for j,x in enumerate(X)) for b in range(1<<(r-1)) if 1<=b.bit_count()<=2} for w in [a,allbits^a] if w not in (0,allbits) for c in cols)
S=[]
for r,D,a,rows,y in candidates():
 if not filterC(r,rows,y):S.append((r,D,a))
print('survive',len(S),S[:9])
