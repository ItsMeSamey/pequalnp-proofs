from pathlib import Path
import os, sys, time, signal, fcntl, subprocess, hashlib, zipfile, tempfile, json, psutil, shutil
base=Path('/workspace/scratch/threshold-star-window')
out=Path(__file__).resolve().parent
checker='/workspace/scratch/syn_pruning/bank11/drat-trim'
files=['six-dirty-three-private-selected-drat.zip']
sha=lambda b:hashlib.sha256(b).hexdigest()
tmp=tempfile.TemporaryDirectory(dir='/dev/shm',prefix='d4-independent-')
wd=Path(tmp.name)
archives=[zipfile.ZipFile(base/f) for f in files]
for j,z in enumerate(archives):
    for f in z.namelist():
        if (f.endswith(('.py','.json','.log')) and not f.startswith('/')):
            p=wd/str(j)/f;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(z.read(f))
def task(j,name,cwd,cmd,proof=None):
    return (j,name,cwd,cmd,proof)
from itertools import combinations,product
roster=[(mode,b,hs,e) for mode in ('ext','hub') for b in (3,4) for hs in combinations(range(6),3) for e in [6]+[j for j in range(6) if j>max(hs)]]
indices={i for i,(mode,b,hs,e) in enumerate(roster) if min(hs)>=b-2}
assert len(roster)==140 and len(indices)==40
assert {f'selected/{i}.drat.gz' for i in indices}=={f for f in archives[0].namelist() if f.endswith('.drat.gz')}
assert sha((base/files[0]).read_bytes())=='6fe610ab8b8e1977062f17f26531dd077c8962977f20c14279aa9e3e140c5f39'
tasks=[task(0,str(i),'',['selreplay.py',str(i),checker],f'selected/{i}.drat.gz') for i in sorted(indices)]
lock=os.open('/workspace/scratch/pnp-native-search.lock',os.O_RDWR|os.O_CREAT)
result=out/'results.jsonl'
past={r['name'] for v in result.read_text().splitlines() if (r:=json.loads(v))['rc']==0} if result.exists() else set()
for j,name,cwd,cmd,pp in tasks:
    if name in past:continue
    while (out/'PAUSE').exists():time.sleep(1)
    z=archives[j];root=wd/str(j);gzh=None
    if pp:
        blob=z.read(pp);gzh=sha(blob);p=root/pp;p.parent.mkdir(parents=True,exist_ok=True);p.write_bytes(blob);del blob
    log=out/(name+'.log');peak=0;chunks=0
    with log.open('w') as w:
        fcntl.flock(lock,fcntl.LOCK_EX)
        env=dict(os.environ,TMPDIR=str(wd),PYTHONDONTWRITEBYTECODE='1',OMP_NUM_THREADS='1',OPENBLAS_NUM_THREADS='1')
        proc=subprocess.Popen([sys.executable,'-B',*cmd],stdout=w,stderr=subprocess.STDOUT,cwd=root/cwd,env=env,start_new_session=True)
        ps=psutil.Process(proc.pid);start=time.monotonic();chunks+=1
        observed={};cpu0=0;over=False
        while proc.poll() is None:
            procs=[ps]+ps.children(recursive=True);rss=0
            for q in procs:
                try:
                    rss+=q.memory_info().rss;u=q.cpu_times();observed[q.pid]=u.user+u.system
                except psutil.NoSuchProcess:pass
            peak=max(peak,rss)
            if rss>160*1024**2:
                os.killpg(proc.pid,signal.SIGKILL);over=True;break
            if time.monotonic()-start>=8.0 or sum(observed.values())-cpu0>=7.0 or (out/'PAUSE').exists():
                os.killpg(proc.pid,signal.SIGSTOP)
                fcntl.flock(lock,fcntl.LOCK_UN);time.sleep(1)
                while (out/'PAUSE').exists():time.sleep(1)
                fcntl.flock(lock,fcntl.LOCK_EX);os.killpg(proc.pid,signal.SIGCONT)
                start=time.monotonic();cpu0=sum(observed.values());chunks+=1
            time.sleep(.06)
        rc=proc.wait();fcntl.flock(lock,fcntl.LOCK_UN)
    if pp:(root/pp).unlink()
    r=dict(name=name,rc=rc,proof=pp,gzip_sha256=gzh,transcript_sha256=sha(log.read_bytes()),peak_rss=peak,chunks=chunks,command=cmd,over=over)
    with result.open('a') as f:f.write(json.dumps(r)+'\n')
    print(name,rc,peak,chunks,flush=True)
    time.sleep(.3)
