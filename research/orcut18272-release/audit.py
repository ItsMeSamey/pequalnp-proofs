"""Check issued masks, raw intersections, shard rows, and totals."""
from pathlib import Path
import json,re,hashlib
R=Path(__file__).parent
def need(p,s):
    if not p:raise ValueError(s)
def nums(s):return list(map(int,re.findall(r'\d+',s)))
s=(R/'instance/statement.lean').read_bytes()
need(hashlib.sha256(s).hexdigest()=='9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b','statement hash')
raw=json.loads((R/'instance/raw-masks.json').read_text())
need(raw==nums(re.search(r'\[([^\]]+)\]\.getD',s.decode())[1]),'issued values')
need(len(raw)==11 and all(v<1<<40 and v&65535 and v>>16 for v in raw),'raw mask domain')
for f in ('producer/orcut18272_enum.cpp','independent/replay.cpp'):
    need(raw==nums(re.search(r'\braw\s*=?\s*\{([^}]+)\}',(R/f).read_text())[1]),f)
pairs={a&b for i,a in enumerate(raw) for b in raw[:i]}
need(all(not (v>>16 and v&65535) and (v&65535).bit_count()<=1 for v in pairs),'raw meets')
need({v for v in pairs if 0<v<=65535}=={1<<i for i in range(16)},'singleton taps')
lines=(R/'producer/orcut18272-complete.log').read_text().splitlines()
need(not any(l.startswith('hit ') for l in lines),'producer hit')
p=[nums(l) for l in lines if l.startswith('shard ')]
c=[list(map(int,l.split())) for l in (R/'independent/all-shards.tsv').read_text().splitlines()]
for rows in (p,c):need([r[0] for r in rows]==list(range(55)),'shard indices')
need(all(len(r)==5 and r[1]==1 and r[-1]==0 for r in p),'producer hits')
need(all(len(r)==8 and r[2]==1 and r[3]==r[5]==r[7]==0 for r in c),'chronological hits')
need([r[1] for r in c]==sorted({a|b for i,a in enumerate(raw) for b in raw[:i]}),'first outputs')
need([sum(r[i] for r in p) for i in (1,2,3)]==[55,4555,532653],'producer counts')
need([sum(r[i] for r in c) for i in (2,4,6)]==[55,6040,1140785],'independent counts')
need((R/'independent/controls.log').read_text()=='640 cover controls passed; 55 initial OR outputs\n','controls')
print('Verified source masks and raw meets, receipts for all 55 shards, and zero hits.')
