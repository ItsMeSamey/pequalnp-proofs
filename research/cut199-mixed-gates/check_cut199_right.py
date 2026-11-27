"""Check the supplied cut-199 encoding against graph truth reconstructed from issued rows."""
import hashlib,itertools,json,re
from functools import reduce
from operator import or_
from pathlib import Path
D=Path(__file__).resolve().parent
def require(ok,message):
    if not ok:raise ValueError(message)
src=(D/'issued18272.txt').read_bytes()
require(hashlib.sha256(src).hexdigest()=='9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b','source identity')
raw=list(map(int,re.findall(r'\((\d+) : ℕ\)',re.search(r'x5 ↑x7 = \[(.*?)\]\.getD',src.decode())[1])))
graph=[tuple(i for i,v in enumerate(raw) if v>>bit&1) for bit in range(16)]
require(len(raw)==11 and all(len(p)==2 for p in graph) and len(set(graph))==16,'edge masks')
left=[i for i in range(11) if 199>>i&1];right=[i for i in range(11) if not 199>>i&1]
def expand(k,order):return {v for i,v in enumerate(order) if k>>i&1}
def edge_present(s):return any(x in s and y in s for x,y in graph)
rows=[sum(int(edge_present(expand(a,right)|expand(b,left)))<<b for b in range(32)) for a in range(64)]
data=(D/'cut199-right-model.json').read_bytes();m=json.loads(data);codes=m['codes']
require((left,right)==(m['left'],m['right']) and len(codes)==64 and all(type(v)==int and 0<=v<32 for v in codes),'encoding')
covers=[(a,a|1<<i) for a in range(64) for i in range(6) if not a>>i&1]
require(all(codes[a]&~codes[b]==0 for a,b in covers),'nonmonotone source cube edge')
pairs=list(itertools.product(range(64),repeat=2))
comparable=[(a,b) for a,b in pairs if codes[a]&~codes[b]==0]
require(all(rows[a]&~rows[b]==0 for a,b in comparable),'incompatible profile comparability')
decoder=[reduce(or_,(rows[a] for a in range(64) if codes[a]&~k==0),0) for k in range(32)]
require(all(decoder[codes[a]]==rows[a] for a in range(64)),'decoder mismatch')
print(dict(sha256=hashlib.sha256(data).hexdigest(),cube_edges=len(covers),ordered_pairs=len(pairs),comparable=len(comparable),codes=len(set(codes)),profiles=len(set(rows)),equal_profile_unequal_code_pairs=sum(rows[a]==rows[b] and codes[a]!=codes[b] for a,b in pairs)))
