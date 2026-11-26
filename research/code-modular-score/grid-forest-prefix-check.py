"""Check the finite-word decoder on seeded non-strict monotone charge chains."""
from graphlib import TopologicalSorter
from itertools import accumulate
from operator import xor
from random import Random

rng = Random(81)
pairs_checked = 0
for trial in range(160):
    row_sizes = [rng.randrange(2, 7) for _ in range(3)]
    col_sizes = [rng.randrange(2, 7) for _ in range(3)]
    sizes = row_sizes + col_sizes
    sign = [rng.choice([-1, 1]) for _ in sizes]
    # A spanning tree on three row and three column bands.
    edges = [(0, 3), (1, 3), (1, 4), (2, 4), (2, 5)]
    order = TopologicalSorter()
    def record(sequence):
        for token in sequence:
            order.add(token)
        for first, second in zip(sequence, sequence[1:]):
            order.add(second, first)
    for v, size in enumerate(sizes):
        record([(v, i) for i in range(size)][::sign[v]])
    all_events = {}
    for a, b in edges:
        rr = list(range(sizes[a]))[::sign[a]]
        cc = list(range(sizes[b]))[::sign[b]]
        i = j = 0
        events = []
        while True:
            if rng.randrange(3): events.append((rr[i], cc[j], rng.randrange(1, 16)))
            if i+1==len(rr) and j+1==len(cc): break
            if j+1==len(cc) or (i+1<len(rr) and rng.randrange(2)): i+=1
            else: j+=1
        cuts = {}
        for axis, coord in [(a, 0), (b, 1)]:
            for pos in range(sizes[axis]):
                t=sum((p[coord]<=pos if sign[axis]>0 else p[coord]>pos) for p in events)
                cuts[(axis,pos)]=t
        merged=sorted(cuts,key=lambda p:(cuts[p],p[0],sign[p[0]]*p[1]))
        record(merged)
        prefix=[0]+list(accumulate((v for _,_,v in events),xor))
        all_events[a,b]=(events,cuts,prefix)
    index={tok:i for i,tok in enumerate(order.static_order())}
    for a in range(3):
      for b in range(3,6):
       for i in range(sizes[a]):
        for j in range(sizes[b]):
         direct=decoded=0
         for (aa,bb),(events,cuts,prefix) in all_events.items():
          for r,c,w in events:
           if (aa,r)<=(a,i) and (bb,c)<=(b,j): direct ^= w
          if aa>a or bb>b: continue
          total=prefix[-1]
          if aa<a and bb<b: decoded ^= total; continue
          if aa==a: row=prefix[cuts[a,i]]
          if bb==b: col=prefix[cuts[b,j]]
          if aa<a: decoded ^= col if sign[b]>0 else total^col; continue
          if bb<b: decoded ^= row if sign[a]>0 else total^row; continue
          rfirst=index[a,i]<index[b,j]
          if sign[a]>0 and sign[b]>0: contribution=row if rfirst else col
          elif sign[a]<0 and sign[b]<0: contribution=total^(col if rfirst else row)
          elif sign[a]>0: contribution=0 if rfirst else row^col
          else: contribution=row^col if rfirst else 0
          decoded ^= contribution
         assert direct==decoded
         pairs_checked+=1
print("160 labelled forests;",pairs_checked,"prefix entries reproduced")
