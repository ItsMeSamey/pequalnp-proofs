"""Bind the consumer source to the upstream bytes without replaying cell witnesses."""
import hashlib,json,re,sys
from pathlib import Path
def sha(b):return hashlib.sha256(b).hexdigest()
def require(v,msg):
    if not v:raise ValueError(msg)
def verify(root):
    def raw(f):return (root/f).read_bytes()
    public=raw('fixture-originals/pnp-official-20579-public.json')
    circuit=raw('fixtures-enriched/source-circuit.json')
    require(sha(public)=='a875746e0199324bc110e968ec84b07ea551b573b44d3d11b5beec021bde0877','public asset')
    require(sha(circuit)=='77e03122cec007ad85fdb752649fa2f19b4f65cf5d06317a66e411e68009a062','physical candidate')
    issued=json.loads(public)['gap'];st=issued['statement'];sf=raw('fixtures-enriched/issued-statement.txt')
    require(sf==st.encode()+b'\n' and issued['id']=='L-meta-20579','issued statement')
    source=raw('Enriched30Data.lean');require(source==raw('fixtures-enriched/Enriched30Data.lean'),'fixture bytes')
    lean=source.decode();rows=[int(x,16) for x in re.findall(r'0x[0-9a-fA-F]+',st)]
    require(rows==json.loads(re.search(r'def rows : List Nat := (\[[0-9, ]+\])',lean)[1]) and len(rows)==32,'row words')
    m=re.search(r'gates := \[(.*?)\]\s+output := (\d+)',lean,re.S);pat=r'⟨\.(and|or|not),\s*(\[[0-9, ]*\])⟩'
    require(not re.sub(pat,'',m[1]).strip(' \n\t,'),'unparsed gate')
    gates=[dict(op=o,inputs=json.loads(p)) for o,p in re.findall(pat,m[1])]
    net=json.loads(circuit)['net']
    require(gates==net['gates'] and int(m[2])==net['output']==233 and len(gates)==170,'gate order, pin order or output')
    closure={}
    def visit(n):
        if n in closure:return
        f=root/(n.replace('.','/')+'.lean')
        if not f.is_file():return
        data=f.read_bytes();closure[n]=sha(data)
        for names in re.findall(r'(?m)^(?:public )?import ([^\n]+)',data.decode()):
            for child in names.split():visit(child)
    visit('Enriched30ActualCost')
    require('Enriched30Data' in closure and 'Enriched30RetainedBinding' in closure,'consumer binding')
    return dict(theorems=['Enriched30ActualCost.physical_size_floor','Enriched30ActualCost.physical_live_floor'],
      scope='Restricted 30-port physical decoder. The receipt verifies source bytes; kernel attestation belongs to the release steward.',
      public_asset_sha256=sha(public),issued_statement_file_sha256=sha(sf),
      graph_1024_row_major_uint8_sha256=sha(bytes((r>>c)&1 for r in rows for c in range(32))),
      graph_128_bytes_uint32_rows_little_endian_sha256=sha(b''.join(r.to_bytes(4,'little') for r in rows)),
      candidate_raw_sha256=sha(circuit),gates=170,output=233,fixture_sha256=sha(source),
      consumer_source_sha256=closure['Enriched30ActualCost'],recursive_local_source_count=len(closure),
      recursive_local_source_map_sha256=sha(json.dumps(closure,sort_keys=True,separators=(',',':')).encode()))
if __name__=='__main__':print(json.dumps(verify(Path(sys.argv[1])),indent=2))
