from pathlib import Path
import ast, hashlib, itertools, json, re, zipfile
from collections import Counter

src = Path('/workspace/scratch/synthesis_new/allpresent-spine274.zip')
pub = Path('/workspace/pnp-research/research/seed-obstructions/raw-width/size33/cumulative-0340')
getids = lambda s: set(map(int, s.split()))
def names(mask):
    return frozenset(i for i in range(mask.bit_length()) if mask >> i & 1)
def swap(items, bij):
    return frozenset(bij[i] for i in items)
def bits(items):
    return sum(1 << i for i in items)
with zipfile.ZipFile(src) as z:
    statement=json.loads(z.read('L-meta-18968.json'))['formal_statement']
    table=[json.loads(line) for line in z.read('remaining.jsonl').splitlines()]
    roster=getids(z.read('t0-remaining-336.ids'))
    expected={int(line.split(' ',1)[0]):ast.literal_eval(line.split(' ',1)[1]) for line in z.read('receipt.log').decode().splitlines()[1:]}
assert hashlib.sha256(statement.encode()).hexdigest()=='d5fbefe3ea85033034056aae8ed0b90ecfe428b8a69e3456176309d0c82b54c2'
seeds=[int(''.join(x.zfill(19) for x in re.findall(r'\((\d+) : ℕ\)',g))) for g in re.findall(r'\[([^]]+)\]',statement)]
direct={int(k):int(v) for k,v in re.findall(r'x1 \((\d+) : ℕ\) = \((\d+) : ℕ\)',statement)}
samples=[]
for row in range(676):
    base=row-row%13
    points=frozenset(j for j in range(13) if seeds[0] >> (base+(row-j)%13) & 1)
    tags=frozenset(j for j in range(7) if seeds[1] >> (base+(row-6-j)%13) & 1)
    status='+' if (direct[88]&~direct[54])>>row&1 else ('-' if not (direct[88]>>row&1) else 's')
    samples.append((points,tags,status))
assert Counter(s for _,_,s in samples)=={'+':28,'-':624,'s':24}
pos=[(p,t) for p,t,s in samples if s=='+']
neg=[(p,t) for p,t,s in samples if s=='-']
assert all(len(p)==len(t)==1 for p,t in pos)
adj={i: frozenset(next(iter(t)) for p,t in pos if i in p) for i in range(13)}
rare={p:next(iter(t)) for p,t in adj.items() if len(t)==1}
ordp=sorted(adj.keys()-rare.keys())
def chart(q):
    u=rare[q]
    P={(p&set(ordp),t-{u}) for p,t in pos if p<=set(ordp) and u not in t}
    N={(p&set(ordp),t-{u}) for p,t in neg if q in p}
    assert len(P)==21 and len(N)==90
    return P,N
baseq=1
baseP,baseN=chart(baseq)
def maps(q):
    P,N=chart(q)
    for tgt in itertools.permutations(sorted(set(range(7))-{rare[baseq]})):
        b=dict(zip(sorted(set(range(7))-{rare[q]}),tgt))
        m={}
        for p in ordp:
            a=swap(adj[p]-{rare[q]},b)
            matches=[r for r in ordp if adj[r]-{rare[baseq]}==a]
            if len(matches)!=1:break
            m[p]=matches[0]
        if len(m)!=9 or len(set(m.values()))!=9:continue
        if {(swap(p,m),swap(t,b)) for p,t in P}!=baseP:continue
        if {(swap(p,m),swap(t,b)) for p,t in N}==baseN:yield m
bijections={q:list(maps(q)) for q in rare}
assert all(len(v)==6 for v in bijections.values())
valid={(),(9,),(20,),(9,20),(9,130),(9,33),(20,33)}
seen={}
for i,t,E,R,C in table:
    if t or i not in roster or R!=8191:continue
    assert i not in seen and not E
    compounds=[names(v) for v in C]
    def flags(p,t):
        return frozenset([('p',v) for v in p]+[('t',v) for v in t]+[('c',bits(v)) for v in compounds if p&v])
    FP=[flags(p,t) for p,t in pos]
    FN=[flags(p,t) for p,t in neg]
    hits=[]
    for q,u in rare.items():
        parent=[v for v in compounds if q in v]
        if len(parent)!=1:continue
        c=parent[0]
        companion=c-{q}
        if len(companion)!=1 or not companion<=set(ordp) or u in adj[next(iter(companion))]:continue
        keep=[v for v in compounds if v!=c]
        if any(not(v&set(ordp)) for v in keep):continue
        projected={v&set(ordp) for v in keep if len(v&set(ordp))>1}
        orbit=min(tuple(sorted(bits(ordp.index(a) for a in swap(v,b)) for v in projected)) for b in bijections[q])
        if orbit not in valid:continue
        hi={('p',q),('c',bits(c))}
        lo={('t',u)}|{('p',v) for v in rare if v!=q}
        assert len(hi|lo)==6
        assert {('p',q),('c',bits(c)),('t',u)}==flags({q},{u})
        assert not any(q in p and u in t for p,t in neg)
        assert all(any(w-n=={('t',u)} for n in FN) for w in FP if ('t',u) in w)
        for p,t in pos:
            if p=={q}:continue
            assert bool(p&c)==bool(p&companion)
        for p,t in pos:
            if p<=set(ordp) and u not in t:
                assert flags(p,t)<=((flags(p,t)-lo)|hi)
        NS=set()
        for p,t in neg:
            if q not in p:continue
            assignment=(flags(p&set(ordp),t-{u})-lo)|hi
            assert assignment<=flags(p,t)
            NS.add(frozenset(assignment-hi))
        unpinned=flags(set(range(13)),set(range(7)))-hi-lo
        assert set.union(set(),*NS)==set(unpinned)
        hits.append((1<<q,bits(c),orbit))
    if hits:seen[i]=hits
assert seen.keys()==expected.keys() and all(set(h)==set(expected[i]) for i,h in seen.items())
old=getids((pub/'t0-remaining-300.ids').read_text())
assert roster==getids((pub/'t0-remaining-336.ids').read_text())
assert not (seen.keys()-old)
remaining=old-seen.keys()
assert remaining==getids((pub/'t0-remaining-26.ids').read_text())
assert len(getids((pub/'t1-remaining-4.ids').read_text()))==4
print('cases',len(seen),'pivots',sum(map(len,seen.values())),'new',len(old)-len(remaining),'remaining',len(remaining),'remaining t1',4)
print('charts',Counter(orb for hits in seen.values() for q,c,orb in hits))
