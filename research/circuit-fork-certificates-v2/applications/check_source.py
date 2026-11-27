"""Bind each application manifest to its physical source and care relation."""
from hashlib import sha256
import json
from pathlib import Path
import runpy
import sys

ROOT = Path(__file__).resolve().parent
sys.path.insert(0,str(ROOT/'shared'))
from verify_marker_geometry import replay

def require(value, message):
    if not value:
        raise ValueError(message)

def load_application(path):
    manifest = json.loads(path.read_text())
    require(manifest['schema']=='scalar-tail-application/v1','application schema')
    for entry in manifest['sources'].values():
        source = (path.parent/entry['file']).resolve()
        require(source.is_relative_to(ROOT),'source must be inside applications')
        require(sha256(source.read_bytes()).hexdigest()==entry['sha256'],'application source pin')
    def source(name):
        return path.parent/manifest['sources'][name]['file']
    if manifest['geometry']=='six-prefix':
        runpy.run_path(str(path.parent/'verify_projection.py'))
        fixed = 143
    elif manifest['geometry']=='four-prefix':
        replay(source('positive'),source('marker'),source('control'))
        fixed = 141
    elif manifest['geometry']=='truth-table':
        fixed=0
    else:
        raise ValueError('unknown physical application')
    fixtures={}
    for model in manifest['interfaces']:
        receipt=json.loads(source(model['source']).read_text())
        rows=receipt['care']
        normalized=json.dumps(sorted(rows),separators=(',',':')).encode()
        require(sha256(normalized).hexdigest()==model['care_sha256'],'canonical care pin')
        require(len(rows)==len(dict(rows))==model['patterns'],'care cardinality')
        require(sum(y for x,y in rows)==model['positives'],'positive labels')
        require(all(type(x) is int and 0<=x<1<<model['wire_count'] and type(y) is int and y in (0,1) for x,y in rows),'care range')
        fixtures[model['id']]=dict(rows)
    budget=manifest['budget']
    require(budget['fixed_physical']==fixed and budget['tail_cap']==budget['physical_target']-fixed and
            budget['tail_lower_bound']==budget['tail_cap']+1,'budget arithmetic')
    require(manifest['scope']['physical_lower_bound']==fixed+budget['tail_lower_bound'],'physical bound')
    return manifest,fixtures
