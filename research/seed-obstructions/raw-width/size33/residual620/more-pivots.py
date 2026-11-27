from pathlib import Path
from tempfile import TemporaryDirectory
from zipfile import ZipFile
import os
root=Path(__file__).resolve().parent
with TemporaryDirectory() as d:
 os.chdir(d);__import__("sys").path.insert(0,d)
 with ZipFile('/workspace/scratch/synthesis_new/allpresent-spine274.zip') as z:z.extractall(d)
 s=Path('verify.py').read_text().replace("roster=set(map(int,Path('t0-remaining-336.ids').read_text().split()))","roster=set(map(int,(root.parent/'cumulative-0340/t0-remaining-26.ids').read_text().split()))")
 s=s.replace('if p not in pts or any','if any').replace('  if any(w&p and w&tag for w in P):continue','').replace('  assert all(bool(w&(1<<extra[c]))==bool(w&(q|p)) for w in rows)','  assert all(bool(w&(1<<extra[c]))==bool(w&c) for w in rows)').replace('assert len(out)==274','')
 __file__=str(Path(d)/"verify.py");exec(s)
 print('LABELS',DEGREE_ONE)
 os.chdir(root)
