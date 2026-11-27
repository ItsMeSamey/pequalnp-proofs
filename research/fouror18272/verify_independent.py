"""Bind the independent archive and check every per-second replay receipt."""
from pathlib import Path
import hashlib
import json
import re
import tarfile

ROOT=Path(__file__).resolve().parent
def need(ok,what):
    if not ok:raise ValueError(what)
def digest(blob):return hashlib.sha256(blob).hexdigest()
archive=ROOT/'independent/18272-four-or-independent.tar.gz'
need(digest(archive.read_bytes())=='b75500603ca8aa1051e1a59458bbd61860958e7b11794ad996fafd76cc7b3cb5','independent archive hash')
producer=json.loads((ROOT/'producer-index.json').read_text())
conf=json.loads((ROOT/'independent/confirmation.json').read_text())
with tarfile.open(archive) as t:
    def read(name):return t.extractfile('18272-four-or-independent/'+name).read()
    blob=read('reviewed-shards.json')
    need(digest(blob)=='11fbd0ff8c2f8132aef9a7e891ec65281ee7a61837f91e4ce9627e37867e6952','review rows hash')
    rows=json.loads(blob)
    need(rows==conf['shards'] and len(rows)==len(producer)==55,'frozen review binding')
    maskstr=re.search(r'inputs\{([^}]+)',read('replay.cpp').decode())[1]
    need(list(map(int,maskstr.split(',')))==json.loads((ROOT/'instance/raw-masks.json').read_text()),'independent inputs')
    for f,(row,p) in enumerate(zip(rows,producer)):
        need(row['first']==p['first']==f and row['first_mask']==p['first_mask'],'first branch')
        ls=read(f'S{f}.tsv').decode().splitlines()
        second={};end=None
        for line in ls:
            w=line.split()
            if w[:1]==['second']:
                ff,s,n3,n4,hits=map(int,w[1:])
                need(ff==f and s>=0 and s not in second and n3>=0 and n4>=0 and hits==0,'independent second row')
                second[s]=(n3,n4)
            elif w[:1]==['end']:
                ff,lo,hi,nn=map(int,w[1:])
                need(ff==f and 0<=lo<=hi and nn>=0 and (end is None or end==nn),'end record')
                end=nn
            else:raise ValueError('unknown independent record')
        need(end==p['second_prefixes']==row['second_prefixes'] and set(second)==set(range(end)),'second coverage')
        third=sum(a for a,b in second.values());fourth=sum(b for a,b in second.values())
        need(third==row['third_leaves']==p['third_leaves'],'third coverage')
        need(fourth==row['raw_fourths'] and fourth+row['signed_adjustment']==p['fourth_states'],'fourth coverage')
        need(row['signed_adjustment']==0 and row['hits']==0 and row['reviewed'] is True,'independent review')
need(sum(r['raw_fourths'] for r in rows)==85164145,'fourth total')
print('Independent semantic receipts agree for 55 first branches and 85,164,145 fourth states.')
