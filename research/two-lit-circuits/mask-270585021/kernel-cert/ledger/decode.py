from pathlib import Path
counts=(0,727,415,41,0)
allkeys=set()
for t,size in enumerate(counts):
    data=Path(f'table{t}.bin').read_bytes()
    pos=0; keys=set()
    while pos<len(data):
        d,b,n=data[pos:pos+3]; pos+=3
        assert d<=b+1 and pos+3*d<=len(data)
        values=tuple(int.from_bytes(data[i:i+3],'little') for i in range(pos,pos+3*d,3))
        pos+=3*d
        assert tuple(sorted(set(values)))==values and all(0<x<2**21-1 for x in values)
        keys.add((b,n,values))
    assert len(keys)==size and pos==len(data)
    allkeys |= keys
print(sum(counts),'per-root exact expansion keys;',len(allkeys),'distinct across roots')
