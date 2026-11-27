from graph import E,Z,V
from functools import cache
from pathlib import Path
from collections import Counter
import json
@cache
def repair(p):
 ed=[a for i,a in enumerate(E) if p>>i&1]
 return len(ed)-1+min(s.bit_count() for s in range(1024) if all(e&s for e in ed))
def eligible(k):
 out={}
 for code,(hot,leaves,expr) in json.loads(Path(f'pareto-{k}.json').read_text()).items():
  m=int(code);p=m&8191;n=m>>13
  if hot or leaves<=5 or n==65535 or repair(p)<=leaves-1:continue
  out[m]=(leaves,expr)
 return out
