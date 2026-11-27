"""Replay independent encoding audits and independently validate both DRAT proofs."""
import argparse,hashlib,os,shutil,subprocess,sys,tempfile
from pathlib import Path
root=Path(__file__).resolve().parent
ap=argparse.ArgumentParser();ap.add_argument('--audit-only',action='store_true');ap.add_argument('--checker',type=Path);ap.add_argument('--compile-checker',action='store_true')
args=ap.parse_args()
if not __debug__:raise RuntimeError('Use Python with assertions enabled')
for row in (root/'SHA256SUMS').read_text().splitlines():
    h,rel=row.split('  ',1)
    if hashlib.sha256((root/rel).read_bytes()).hexdigest()!=h:raise ValueError(rel)
paths={
 '/dev/shm/team04-relaxed170-scc':root/'narrow','/dev/shm/team04-relaxed170-wide':root/'wide',
 '/dev/shm/team04-relaxed170/restart-base-with-static-cycles.json.gz':root/'inputs/restart-base-with-static-cycles.json.gz',
 '/dev/shm/04-merged-terms/joint181-pool-plus-near180.json.gz':root/'inputs/joint181-pool-plus-near180.json.gz',
 '/tmp/pnp-official-20579-public.json':root/'inputs/pnp-official-20579-public.json'}
for script in ['audit04scc.py','audit04wide.py']:
    text=(root/'team07'/script).read_text()
    for old,new in paths.items():text=text.replace(repr(old),repr(str(new)))
    exec(compile(text,script,'exec'),{'__name__':'__main__'})
if args.audit_only:sys.exit()
with tempfile.TemporaryDirectory() as tmp:
    if args.compile_checker:
        checker=Path(tmp)/'drat-trim'
        subprocess.run([os.environ.get('CC','cc'),'-O2',str(root/'checker/drat-trim.c'),'-o',str(checker)],check=True)
    else:checker=args.checker.resolve() if args.checker else root/'checker/drat-trim'
    for family in ('narrow','wide'):
        d=root/family
        r=subprocess.run([str(checker),str(d/'branch-0000.cnf'),str(d/'branch-0000.drat')],stdout=subprocess.PIPE,stderr=subprocess.STDOUT)
        if r.returncode or b's VERIFIED' not in r.stdout:raise RuntimeError(r.stdout.decode(errors='replace'))
        print(f'{family} DRAT VERIFIED')
