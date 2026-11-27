from itertools import combinations
cases={'K33':(56,56,56,7,7,7),'six':(52,56,41,38,35,31),'eight':(196,248,185,230,134,14,11,31)}
for name,rows in cases.items():
    words=[]
    n=len(rows)
    for s in range(3,1<<n,4):
        if all((s&r).bit_count()%2 for i,r in enumerate(rows) if s>>i&1):
            words.append(s)
    minimal=[w for w in words if all(v&w!=v for v in words if v!=w)]
    for i,j in combinations(range(n),2):
        live=((1<<n)-1)^(1<<i)^(1<<j)
        seen=live&-live
        for _ in rows:
            for k,r in enumerate(rows):
                if seen>>k&1:seen|=r&live
        assert seen==live
    print(name,'all odd pinned masks',words,'minimal masks',minimal)
