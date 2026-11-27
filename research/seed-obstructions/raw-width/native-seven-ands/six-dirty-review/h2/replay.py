from pathlib import Path
import os, sys, time, signal, fcntl, subprocess, hashlib, zipfile, tempfile, json, psutil, shutil
base=Path('/workspace/scratch/threshold-star-window')
out=Path(__file__).resolve().parent
checker='/workspace/scratch/syn_pruning/bank11/drat-trim'
files=['six-dirty-two-private-selected-drat.zip']
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
roster=list(product(combinations(range(5),2),('shared','cross'),(2,3,4)))
indices={i for i,((h,k),mode,b) in enumerate(roster) if h >= (2 if b==4 else 1)}
assert len(indices)==30 and {f'proof-{i}.gz' for i in indices}=={f for f in archives[0].namelist() if f.startswith('proof-') and f.endswith('.gz')}
assert sha((base/files[0]).read_bytes())=='21cba4a0441e2833b4a6c16faf060d4c74c943a1ebaeffd676e22c224c927cd8'
tasks=[task(0,str(i),'',['verify_release.py','--checker',checker,str(i)],f'proof-{i}.gz') for i in sorted(indices)]
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
