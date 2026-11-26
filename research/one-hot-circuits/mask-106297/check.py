import json
from pathlib import Path
gates = [
    ["or",0,1],["or",7,8],["and",9,10],
    ["or",2,3],["and",12,5],["and",2,6],
    ["or",4,11],["or",15,13],["or",16,14],
]
m=106297
rows = [{j for j in range(5) if m >> (5*i+j) & 1} for i in range(4)]
cols = [{i for i in range(4) if j in rows[i]} for j in range(5)]
for shore in (rows,cols):
    assert all(any(not a <= b for b in shore) for a in shore)
assert {1,2} <= rows[2] and 1 in rows[3] and 2 not in rows[3]
assert all(3 not in rows[i] for i in (2,3))
assert all(0 not in cols[j] for j in (1,2))
mask=0
for i in range(4):
    for j in range(5):
        w=[i==k for k in range(4)] + [j==k for k in range(5)]
        for op,a,b in gates:
            assert 0<=a<len(w) and 0<=b<len(w)
            w.append(w[a] and w[b] if op=="and" else w[a] or w[b])
        mask|=int(w[-1])<<(5*i+j)
assert mask == m and len(gates)==9
Path("upper9.json").write_text(json.dumps(gates)+"\n")
print("9 distinct mandatory flags; cold corner; upper 9 gates; 20/20 cells; mask",mask)
