from pathlib import Path
cases=[(i,j) for i in range(6) for j in range(i,6)]
raw=270585021
gate=[('|',0,1),('!',6,6),('&',5,7),('|',2,3),('|',0,9),('&',1,10),('&',4,9),('|',8,11),('|',12,13),('!',14,14)]
def simulate(i,j,replacement=None):
    v=[s in (i,j) for s in range(6)]
    for k,(op,a,b) in enumerate(gate):
        if replacement is not None and k==replacement[0]:v.append(v[replacement[1]])
        else:v.append((not v[a]) if op=='!' else v[a] and v[b] if op=='&' else v[a] or v[b])
    return v[-1]
def dense(replace=None):
    return sum(simulate(i,j,replace)<<k for k,(i,j) in enumerate(cases))
target=sum(((raw>>(6*i+j))&1)<<k for k,(i,j) in enumerate(cases))
assert dense()==target
# For each variable find singleton/pair assignments distinguished solely by it.
for a in range(6):
    witness=next((p,q) for p in cases for q in cases if set(p)^set(q)=={a} and simulate(*p)!=simulate(*q))
    print(a,witness)
neighbors=[(k,alias,dense((k,alias))) for k in range(10) for alias in range(6+k) if (target^dense((k,alias))).bit_count()==1]
print('single cell neighbors',neighbors[:24])
keys={(int(b),int(t),int(f)) for b,t,f in (l.split() for l in Path('keys.tsv').read_text().splitlines())}
assert keys=={(9-t,t,63) for t in range(5)}
seen=set()
for l in Path('result.log').read_text().splitlines():
    m,b,t,f,res,*_=l.split()
    assert int(m)==target and res=='UNSAT'
    seen.add((int(b),int(t),int(f)))
assert seen==keys
lines=Path('adjacent9.log').read_text().splitlines()
assert lines[0].split()[:5]==['302719','7','2','63','SAT']
known={sum((a in q)<<k for k,q in enumerate(cases)) for a in range(6)}
for l in lines[1:]:
    a,op,b,eq,y=l.split();a,b,y=map(int,(a,b,y))
    assert a in known and (op=='!' or b in known)
    assert y=={'!':(2**21-1)^a,'&':a&b,'|':a|b}[op]
    known.add(y)
assert len(lines)==10 and y==302719
