"""Tighten the published eleven-bank enumeration to a 13-point-gate budget."""
from pathlib import Path
from hashlib import sha256
import tempfile
import subprocess
import sys

def main():
    base=Path(sys.argv[1]).resolve()/'eleven-irreducible'
    sys.path.insert(0,str(base))
    from samples import raw_samples
    p,n=raw_samples(base/'L-meta-18968.json')
    stars=[sum(1<<((6+j+d)%13) for d in (0,1,3,9)) for j in range(7)]
    rows={(a&8191,b&8191) for a in p for b in n if not ((a>>13)&~(b>>13))}
    rel=sorted((a,b) for a,b in rows if not any(c==a and b!=d and not b&~d for c,d in rows))
    assert len(rel)==1323
    data=' '.join(map(str,stars))+'\n'+'0 0\n'*7+''.join(f'{a} {b}\n' for a,b in rel)
    family=Path(sys.argv[2]).read_bytes()
    assert sha256(family).hexdigest()=='46867554aad75991fd158f4ce5918c138e236b137eaed9d8f005f828eeb2f2fb'
    with tempfile.TemporaryDirectory() as dirname:
        wd=Path(dirname)
        source=(base/'hereditaryrole.hpp').read_text()
        old='bool(votes.plane[4] | votes.plane[5])'
        assert source.count(old)==1
        (wd/'hereditaryrole.hpp').write_text(source.replace(old,'votes.max() >= 14'))
        (wd/'stream.cpp').write_bytes((base/'stream11simple.cpp').read_bytes())
        subprocess.run(['c++','-O3','-std=c++20','-march=native',wd/'stream.cpp','-o',wd/'stream'],check=True)
        for q in (15,23,27,46,83):
            r=subprocess.run([wd/'stream',str(q),base/f'pairanchors-{q}.txt'],input=data,text=True,stdout=subprocess.PIPE,check=True)
            assert not r.stdout.strip(),q
            print(q,'no irreducible bank at cost 13',flush=True)
        (wd/'bound.cpp').write_text('''#include "hereditaryrole.hpp"
#include <cstdio>
using namespace hereditary;
int main(){setup();for(int i=0;i<278;i++){Mask x;for(int& v:x)if(scanf("%d",&v)!=1)return 2;
if(bound<true>(x,x)<14)return 3;}int extra;return scanf("%d",&extra)==1?4:0;}
''')
        subprocess.run(['c++','-O3','-std=c++20',wd/'bound.cpp','-o',wd/'bound'],check=True)
        subprocess.run([wd/'bound'],input=family,check=True)
        print('278 reducible candidates excluded.')
if __name__=='__main__':main()
