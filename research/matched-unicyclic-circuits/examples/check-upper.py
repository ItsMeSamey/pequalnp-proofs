"""Verify the gate lists without external dependencies, from any directory."""
import json
from pathlib import Path

root=Path(__file__).resolve().parent
for name,host in [('adjacent',1),('opposite',3)]:
    d=json.loads((root/(name+'.json')).read_text())
    expected={tuple(sorted((i,(i+1)%6))) for i in range(6)}|{(0,6),(host,7)}
    assert set(map(tuple,d['edges']))==expected and d['n']==8
    gates=d['gates']
    assert len(gates)==11 and sum(op=='or' for op,_,_ in gates)==7
    for s in range(256):
        v=[bool(s>>i&1) for i in range(8)]
        for op,a,b in gates:
            assert op in ('and','or') and 0<=a<len(v) and 0<=b<len(v)
            v.append((v[a] and v[b]) if op=='and' else (v[a] or v[b]))
        assert v[d['output']]==any((s>>a&1) and (s>>b&1) for a,b in expected)
    print(f'{name}: 11 gates, 4 AND and 7 OR, all 256 assignments verified')
