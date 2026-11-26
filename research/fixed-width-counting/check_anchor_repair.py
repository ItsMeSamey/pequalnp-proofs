from itertools import product,combinations
count=0
for mask in range(1,256):
    allrows=list(product(range(2),repeat=3))
    rows={r for i,r in enumerate(allrows) if mask>>i&1}
    for anchor in [(),(0,),(0,1),(0,1,2)]:
        groups={tuple(r[i] for i in anchor) for r in rows}
        for key in groups:
            part={r for r in rows if tuple(r[i] for i in anchor)==key}
            univ=[{r[j] for r in part if all(y[:j]+(r[j],)+y[j+1:] in part for y in part)} for j in range(3)]
            core=set(product(*univ))
            failed={frozenset([x,y]) for x in part for y in part if any(y[:j]+(x[j],)+y[j+1:] not in part for j in range(3))}
            assert core<=part
            assert part-core <= set().union(*failed)
            assert len(part-core)<=2*len(failed)
            count+=1
print(f"{count} conditional repairs checked")
