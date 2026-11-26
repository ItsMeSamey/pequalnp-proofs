"""Rebuild the q11 ledgers and compare bytes against frozen copies (NetworkX required)."""
from pathlib import Path
import hashlib
import subprocess
import sys
root=Path(__file__).resolve().parent
scripts=[
('degree/t14-34/eleven-atlas.py','degree/t14-34/eleven-atlas.tsv'),
('verification/fourteen-nine-host/q11_peeled_spoilers.py','verification/fourteen-nine-host/q11-peeled-spoilers.tsv'),
('degree/t14-34/eleven-branch-roles.py','degree/t14-34/eleven-branch-roles.tsv'),
('degree/t14-34/eleven-role-debits.py','degree/t14-34/eleven-role-debits.tsv'),
]
for src,output in scripts:
    expected=hashlib.sha256((root/output).read_bytes()).digest()
    subprocess.run([sys.executable,'-B',str(root/src)],cwd=root,check=True)
    assert hashlib.sha256((root/output).read_bytes()).digest()==expected,output
subprocess.run([sys.executable,'-B',str(root/'degree/t14-34/eleven-small-remotes.py')],cwd=root,check=True)
geometry='geometry/fourteen34/connected-eleven-cuts'
p=subprocess.run([sys.executable,'-B',str(root/(geometry+'.py'))],cwd=root,check=True,stdout=subprocess.PIPE)
assert p.stdout==(root/(geometry+'.tsv')).read_bytes()
subprocess.run([sys.executable,'-B','audit.py'],cwd=root/'fourteen-eleven-four-seven-cert',check=True)
print('q11 portable replay completed')
