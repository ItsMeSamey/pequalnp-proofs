"""Hash the cited sources and validate the directed dependency map; no search replay."""
import argparse
import hashlib
import json
from graphlib import TopologicalSorter
from pathlib import Path

HERE = Path(__file__).resolve().parent
Q = 'fourteen-sixteen-complete-cert/'
J = 'fourteen-seventeen-nonstar-cert/'
U = 'duality/uniform/'
G = {}
def node(key, deps, *paths):
    G[key] = {'requires':deps.split(), 'sources':list(paths)}

node('C8-size19','', 'verification/threshold-eight/eight-proof.md','verification/threshold-eight/checksums.txt')
node('C9-size21','', 'verification/threshold-nine/nine-proof.md','verification/threshold-nine/checksums.txt')
node('OR-tight','C8-size19', Q+'degree/t13-31/or-optimal.md',Q+'verification/threshold-twelve/or-tight.md')
node('C9-four-AND','C8-size19 C9-size21 OR-tight','degree/t13-seven/nine-five/README.md','degree/t13-seven/nine-six/README.md')
node('C10-size24','C8-size19 C9-size21','ten-exact-cert/PROOF.md','ten-exact-cert/SHA256SUMS')
node('C11-size27','C10-size24','eleven-unrestricted-27-cert/PROOF.md','eleven-unrestricted-27-cert/SHA256SUMS')
node('T10-minor','C9-four-AND C10-size24',Q+'degree/t13-seven/ten-minor.md',Q+'degree/t13-seven/ten-three-groups.md',Q+'degree/t13-seven/ten-doubletons.md')
node('local-transfer','',Q+'comb/fourteen-construct/independent-raw-or-increment.md',Q+U+'fourteen-cycle-component-transfer.md')
node('T10-local-forest','T10-minor local-transfer',Q+'degree/t16-cyclic-build/ten-forest.md')
node('two-stars','local-transfer',Q+'degree/t16-pair-stars/two-three-stars.md',Q+'degree/t16-pair-stars/check.py')
node('q16','C8-size19 C9-four-AND C10-size24 C11-size27 OR-tight T10-local-forest two-stars',Q+'SHA256-MANIFEST',Q+'README.md')
node('T10-unrestricted-A7','T10-local-forest two-stars T10-minor',U+'ten-unrestricted-seven-and.md')
node('q17-P5','q16 T10-unrestricted-A7',J+'degree/t17/path-five.md',J+'degree/t17/local-path-floors.md')
node('q17-nonstar','q17-P5 q16',J+'SHA256-MANIFEST',J+'degree/t17/cyclic-extra-edges.md',J+'degree/t17/path-four.md')
node('q17-star','q16 T10-local-forest two-stars',U+'seventeen-star-four-paths.md')
node('T11-cubic','T10-unrestricted-A7 q17-star',U+'eleven-cubic.md')
node('T11-nonstar','T11-cubic q17-nonstar q16',U+'eleven-nonstar.md','degree/t18/nonstars.md')
node('T11-unrestricted-A8','T11-cubic T11-nonstar OR-tight C9-four-AND',U+'eleven-unrestricted-eight-and.md','degree/t18/five-short.md')

def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()
def compute(base):
    order=list(TopologicalSorter({k:v['requires'] for k,v in G.items()}).static_order())
    ancestors={}
    for k in order:
        deps=G[k]['requires']
        ancestors[k]=set(deps).union(*(ancestors[d] for d in deps))
    assert not ancestors['q16'].intersection({'q17-P5','q17-nonstar','q17-star','T10-unrestricted-A7','T11-unrestricted-A8'})
    assert {'q16','T10-unrestricted-A7'}<=ancestors['q17-P5']
    assert {'q17-P5','q17-star','C11-size27'}<=ancestors['T11-unrestricted-A8']
    paths={p for n in G.values() for p in n['sources']}
    for packet in (Q,J):
        for line in (base/packet/'SHA256-MANIFEST').read_text().splitlines():
            digest,name=line.split(maxsplit=1)
            path=packet+name.removeprefix('./')
            if sha(base/path)!=digest: raise ValueError(path)
            paths.add(path)
    graph={'dependency_level':'theorem or historical certificate packet','topological_order':order,'nodes':G}
    return json.dumps(graph,indent=2)+'\n',''.join(f'{sha(base/p)}  {p}\n' for p in sorted(paths))
if __name__=='__main__':
    parser=argparse.ArgumentParser()
    parser.add_argument('--root',type=Path,default=HERE.parents[1])
    parser.add_argument('--write',action='store_true')
    a=parser.parse_args()
    for name,data in zip(('graph.json','sources.sha256'),compute(a.root)):
        p=HERE/name
        if a.write:p.write_text(data)
        elif p.read_text()!=data:raise ValueError(name)
    print('checked theorem DAG, source hashes and both packet manifests')
