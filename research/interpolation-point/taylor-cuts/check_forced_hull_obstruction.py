from itertools import combinations, product

cols=((1,1,0),(2,0,1),(0,2,2),(1,0,0),(0,1,0),(0,0,1))
points=[(s,tuple(sum(x*a[j] for x,a in zip(s,cols))%3 for j in range(3)))
        for s in product((1,2),repeat=6)]
assert all(y!=(0,0,0) for _,y in points)
checks=0
for size in range(3):
    for ids in combinations(range(6),size):
        for values in product((1,2),repeat=size):
            pts=[y for s,y in points if tuple(s[i] for i in ids)==values]
            assert all(len({sum(a*b for a,b in zip(v,y))%3 for y in pts})>1
                       for v in product(range(3),repeat=3) if any(v))
            checks+=1
print(checks,"full conditional hulls; zero target absent")
