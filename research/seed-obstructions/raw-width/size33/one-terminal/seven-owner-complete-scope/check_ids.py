"""Independent historical seven-owner ledger crosscheck."""
from ast import literal_eval
from collections import Counter
from gzip import decompress
from hashlib import sha256
from json import loads
from pathlib import Path
from zipfile import ZipFile

root = Path('/workspace/scratch')
ix = root/'syn_sat/t128-r7-baseline-index.zip'
assert sha256(ix.read_bytes()).hexdigest() == 'b8b3bd25ffd2555a9ed326c9d09fd31435e1a1a9f573e36bb3b840a93e7ddb83'
with ZipFile(ix) as z:
    ledger=list(map(loads,z.read('ledger.jsonl').splitlines()))
    rows=list(map(loads,decompress(z.read('terminal-raw-keys.jsonl.gz')).splitlines()))
    meta=loads(z.read('dependencies.json'))['archives']
    outside=set(map(int,loads(z.read('outside.json'))))
    groups={s:set(ids) for s,ids in loads(z.read('blocks.json')).items()}
for name,digest in meta.values():
    assert sha256(Path(name).read_bytes()).hexdigest()==digest

def source(name):
    return ZipFile(meta[name][0])

names=(129,354,523,1046,2092,4160)
bank={}
inert=set()
for i,(t,e,r,C,_,aliases,g,old) in enumerate(rows):
    if (t,g)!=(1,28):
        continue
    values=[next((y for y in names if y&8133==x&8133),x&8133) for x in C]
    assert values==aliases and not old
    if 0 in values:
        inert.add(i)
        continue
    assert r==8191-e[0]
    w=Counter(values)
    w.update(1<<j for j in range(13) if (8133>>j)&1)
    bank[i]=(tuple(x for x in names if x in w),tuple(sorted((x,v) for x,v in w.items() if v>1)))
assert set(bank)=={l[0] for l in ledger} and len(bank)==len(ledger)==5976 and inert==outside and len(inert)==24
for i,c,w,s,b in ledger:
    assert i in groups[s] and bank[i]==(tuple(c),tuple(map(tuple,w)))
assert sum(map(len,groups.values()))==len(bank)
with source('t1-seven-both-cross.zip') as z:
    openids=set(map(int,z.read('both-open.ids').split()))
    both=loads(z.read('both-reasons.json'))
    E={i for i,(c,w) in bank.items() if c==(129,4160)}
    assert set(map(int,both))==E
    for i in E:
        label='both-'+both[str(i)]
        if label=='both-open' and not bank[i][1]:
            label+='-cap16'
        assert i in groups[label]
assert openids==groups['both-open']|groups['both-open-cap16']
with source('one-terminal-seven-two-compounds.zip') as z:
    residual=set(map(int,z.read('remaining.ids').split()))
    assert {i for i,(c,w) in bank.items() if len(c)==2}-residual==groups['pair-initial']
    assert residual-E==groups['pair-virtual']
with source('t1-low-endpoint-anonymous.zip') as z:
    L=literal_eval(z.read('live.txt').decode())
    assert {i for w,ids in L if not w for i in ids}==groups['single-end-wild16']
    assert {i for w,ids in L if w for i in ids}==groups['single-end-low-positive']
assert not openids&groups['single-end-wild16']
with source('t1-three-seven-complete-v2.zip') as z:
    assert {i for j in range(20) for l in z.read(f'ledgers/{j}.log').decode().splitlines() for i in literal_eval(l)[2]}==groups['three']
four=root/'syn_mitm/s28-four-seven-independent.zip'
assert sha256(four.read_bytes()).hexdigest()=='763f7521fa6c31c71570843d4f65ffb86c6bb992efc66d771fe5941f647141c6'
with ZipFile(four) as z:
    got=set()
    for j in range(15):
        c,w,ids,slots=literal_eval(z.read(f'ledgers/{j}.log').decode())
        assert not w and all(bank[i]==(c,w) for i in ids) and got.isdisjoint(ids)
        if slots:
            assert literal_eval(z.read(f'ledgers/joint{j}.log').decode())==(c,w,ids,len(slots),[])
        else:
            assert not z.read(f'ledgers/joint{j}.log')
        got.update(ids)
    assert got==groups['four']
print(len(bank),'included;',len(bank)-len(openids),'excluded;',len(openids),'open;',len(inert),'outside')
print('WILD',sorted(groups['single-end-wild16']))
print('capped two-endpoint',sorted(groups['both-open-cap16']))
