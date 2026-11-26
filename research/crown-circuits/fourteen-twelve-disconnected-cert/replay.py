from pathlib import Path
import csv,gzip,hashlib,subprocess,sys
root=Path(__file__).resolve().parent
with gzip.open(root/'fourteen-eight-cases/component-rows.tsv.gz','rt') as f:
    partitions={tuple(sorted(sum(map(int,c.split(','))) for c in r['component_degree_counts'].split(';'))) for r in csv.DictReader(f,delimiter='\t') if r['vertices']=='12' and r['components']!='1'}
assert len(partitions)==15
p=root/'degree/t14-34'
for stem in ('twelve-disconnected','twelve-marked'):
 out=p/(stem+'.tsv')
 before=hashlib.sha256(out.read_bytes()).digest()
 subprocess.run([sys.executable,'-B',str(p/(stem+'.py'))],cwd=root,check=True)
 assert hashlib.sha256(out.read_bytes()).digest()==before
with (p/'twelve-disconnected.tsv').open() as f:
 rows=list(csv.DictReader(f,delimiter='\t'))
assert len(rows)==106
with (p/'twelve-marked.tsv').open() as f:
 rem={r['graphs']:r['possible_marks'] for r in csv.DictReader(f,delimiter='\t') if r['possible_marks']!='-'}
assert rem=={'G18,GhCK?K':'0:0,0:1,0:2,0:3','G16,G16,G18':'2:0,2:1,2:2,2:3'}
print('15 order partitions; 106 hosts, 104 generic exclusions, two reviewed terminal rows')
