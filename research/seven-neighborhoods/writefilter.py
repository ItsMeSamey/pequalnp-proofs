import pickle
J=pickle.load(open('seven-jobs.pkl','rb'));L=[sum(1<<((i+d)%13) for d in (0,1,3,9)) for i in range(7)]
with open('filter7.in','w') as f:
 print(*L,file=f)
 for i,(S,G,v,Q,dd) in enumerate(J):
    if Q!=2:continue
    sig=[[t for t,p in G.items() if j in p] for j in range(v)]
    pu=[set(s) for s in sig if set(s)<=set(S)]
    if not any(a.isdisjoint(b) for a in pu for b in pu):continue
    for di,d in enumerate(dd):
        C=L.copy()
        for t,p in zip(S,d):C[t]&=~(1<<p)
        mn=[0]*v
        for t,(x,y) in G.items():mn[x]|=C[t];mn[y]|=C[t]
        mx=[8191]*v
        for t,(x,y) in G.items():mx[x]&=~(mn[y]&~C[t]);mx[y]&=~(mn[x]&~C[t])
        print(i,di,v,*mn,*mx,*C,*(q for t in range(7) for q in G[t]),file=f)
