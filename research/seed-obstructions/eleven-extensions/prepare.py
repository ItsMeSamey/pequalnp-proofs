from pathlib import Path
import sys
from decode import raw_samples,actions
d=Path(__file__).parent;out=Path(sys.argv[1]);p,n=raw_samples(d/'L-meta-18968.json')
gp=actions(p,n)
(out/'actions.dat').write_text(''.join(' '.join(map(str,g))+'\n' for g in gp))
(out/'rows').write_text(' '.join(map(str,[len(p),len(n),*sorted(p),*sorted(n)]))+'\n')
