from pathlib import Path
import re
for d,globs in {3:['d3-double-first.log','d3double-*.log'],4:['d4double-*.log']}.items():
    result={}
    for pat in globs:
        for f in Path('.').glob(pat):
            for line in f.read_text().splitlines():
                m=re.fullmatch(r'(\d+) atoms .* hits (\d+)',line)
                if m:
                    i,v=map(int,m.groups())
                    assert i not in result or result[i]==v
                    result[i]=v
    print(d,'closed',sum(v==0 for v in result.values()),'relaxed candidates',[i for i,v in result.items() if v>0],'first untested',next((i for i in range(6,226) if i not in result),None))
