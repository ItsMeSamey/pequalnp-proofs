from pathlib import Path
exec(Path(__file__).with_name('check-fano-seven-fork-clamp.py').read_text().split('for omissions')[0])
stats=Counter(); remprof=[]
for mis in combinations(range(21),2):
 rem=[m for i,m in enumerate(M) if i not in mis]
 faults=[(h,x) for x in range(12) for h in range(12) if h//6!=x//6 and h not in N[x] and not any(h in m and N[x]&m for m in rem)]
 assert all((x,h) not in faults for h,x in faults)
 if not faults:continue
 for C in coldsets:
  H=set(range(12))-C
  imp=[(h,x) for h,x in faults if h in H and x in H]
  cont={x for h,x in faults if h in H and x in C}
  possi=imp; possc=cont
  for imp in ([[],possi] if possi else [[]]):
   for cont in ([set(),possc] if possc else [set()]):
    alive=set(range(12))-cont
    # optional possible dependence at f_x of extra h with h singleton; expand f_x as x OR h.
    caps=[(1 if v in C else 2)+sum(h==v for h,x in imp) for v in range(12)]
    base=caps[:]
    for c in cont:
     for v in N[c]:
      if imp and (v,next((h for h,x in faults if x==c and h in H),None)) in imp:continue
      caps[v]-=1
    A=[e for e in E if set(e)<=alive]
    # sparse clamped negatives can be tested on smaller proper neighborhoods after pin.
    good=[e for e in A if any(((N[e[0]]|N[e[1]])&alive)-set(e)<=m for m in rem)]
    # If no flag lost, capped formula suffices; print limits.
    ok=False
    HH=[e for e in A if not (set(e)&C)]
    for bits in range(1<<len(HH)):
     lost={e for i,e in enumerate(HH) if bits>>i&1}
     touch={v for e in lost for v in e}
     sc=caps[:]
     for v in touch:sc[v]=min(sc[v],base[v]-1)
     pos=[e for e in A if e not in lost]
     P={v:{b if v==a else a for a,b in pos if v in (a,b)} for v in alive}
     # P4 nonedge outer endpoints must still reject, including same-shore pairs;
     # C4-free ensures nonedge; exact cross nonflags survive all two omissions.
     if any(sc[a]<=1 and sc[b]<=1 and len(P[a])>=2 and len(P[b])>=2 for a,b in pos):continue
     if orientable([e for e in good if e not in lost],sc):ok=True;break
    stats[len(imp),len(cont),ok]+=1
    if ok:remprof.append((mis,C))
assert stats=={(0,0,False):192,(0,1,False):104,(1,0,False):40,(1,1,False):8}
print(stats)
