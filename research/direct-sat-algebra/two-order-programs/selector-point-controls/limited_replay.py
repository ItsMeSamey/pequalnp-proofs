import fcntl,json,os,resource,subprocess,sys,time
from pathlib import Path
here=Path(__file__).resolve().parent
clock=lambda:sum(resource.getrusage(resource.RUSAGE_CHILDREN)[:2])
start=clock()
with (here/'results.jsonl').open('x') as dest:
    for h in (3,5,9):
        for yes in (0,1):
            remaining=int(24-(clock()-start))
            if remaining<1:
                print(json.dumps(dict(h=h,yes=yes,status='capacity cutoff')),file=dest,flush=True)
                continue
            def limits():
                os.nice(15)
                resource.setrlimit(resource.RLIMIT_CPU,(min(6,remaining),min(6,remaining)))
                resource.setrlimit(resource.RLIMIT_AS,(160*1024**2,160*1024**2))
            with open('/workspace/scratch/pnp-native-search.lock','a') as lock:
                fcntl.flock(lock,fcntl.LOCK_EX)
                try:
                    a=subprocess.run([sys.executable,str(here/'compare.py'),str(h),str(yes)],capture_output=True,text=True,timeout=8,preexec_fn=limits)
                    dest.write(a.stdout)
                    if a.returncode: print(json.dumps(dict(h=h,yes=yes,status='process cutoff or error',code=a.returncode,stderr=a.stderr[-500:])),file=dest)
                except subprocess.TimeoutExpired as e:
                    partial=e.stdout or b''
                    dest.write(partial.decode() if isinstance(partial,bytes) else partial)
                    print(json.dumps(dict(h=h,yes=yes,status='wall cutoff')),file=dest)
                dest.flush()
            time.sleep(.12)
print('aggregate child CPU',clock()-start)
