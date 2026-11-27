"""Bounded single-compiler replay; requires the shared compiler lane."""
from pathlib import Path
import hashlib
import os
import subprocess
import time
import sys
import json

src = Path(__file__).resolve().parent
obj = src / 'objects'
logs = src / 'receipts'
obj.mkdir(exist_ok=True)
logs.mkdir(exist_ok=True)
lean = '/home/agent/.elan/toolchains/leanprover--lean4---v4.36.0/bin/lean'
pinned = Path('/workspace/scratch/official24202/numeric/pinned.path').read_text().strip()
env = os.environ | {'LEAN_PATH': str(obj) + ':' + pinned}
for mod in sys.argv[1:]:
    source = src / (mod+'.lean')
    start = time.monotonic()
    peak = 0
    with (logs/(mod+'.log')).open('w') as log:
        p = subprocess.Popen([lean,'-j1','--root='+str(src),'-o',str(obj/(mod+'.olean')),str(source)],env=env,stdout=log,stderr=subprocess.STDOUT)
        old_oom = sum(int(l.split()[1]) for l in Path('/sys/fs/cgroup/memory.events').read_text().splitlines() if l.split()[0] in ('oom','oom_kill'))
        with (logs/(mod+'.memory.jsonl')).open('w') as monitor:
            while p.poll() is None:
                try:
                    def metrics(path):
                        return {t[0].rstrip(':'):int(t[1]) for l in path.read_text().splitlines() if len(t:=l.split())>1 and t[1].isdigit()}
                    proc = Path('/proc',str(p.pid))
                    stats = metrics(proc/'status')
                    roll = metrics(proc/'smaps_rollup')
                    cg = Path('/sys/fs/cgroup')
                    mem = metrics(cg/'memory.stat')
                    peak=max(peak,stats['VmRSS'])
                    rec={'elapsed':round(time.monotonic()-start,3),'VmRSS_KiB':stats['VmRSS'],'RssAnon_KiB':stats.get('RssAnon'),'RssFile_KiB':stats.get('RssFile'),'Pss_Anon_KiB':roll.get('Pss_Anon'),'Pss_File_KiB':roll.get('Pss_File'),'Pss_Shmem_KiB':roll.get('Pss_Shmem'),'RssShmem_KiB':stats.get('RssShmem'),'cgroup_current_B':int((cg/'memory.current').read_text()),'cgroup_anon_shmem_kernel_B':sum(mem.get(k,0) for k in ('anon','shmem','kernel')),'cgroup_events':metrics(cg/'memory.events')}
                    monitor.write(json.dumps(rec)+'\n')
                    monitor.flush()
                    if roll.get("Pss_Anon",0)>563200 or (stats['VmRSS']>2621440 and roll.get("Pss_File",0)<stats['VmRSS']*0.65): p.kill()
                    if rec["cgroup_current_B"]>8455716864 and mem.get("file",0)-mem.get("shmem",0)<805306368: p.kill()
                    if rec["cgroup_anon_shmem_kernel_B"] > int(os.environ["LEAN_CGROUP_NONRECLAIMABLE_LIMIT"]) or sum(rec["cgroup_events"].get(k,0) for k in ("oom","oom_kill")) > old_oom: p.kill()
                except (FileNotFoundError,ProcessLookupError,KeyError): pass
                if peak>3145728 or time.monotonic()-start>25: p.kill()
                time.sleep(.16)
        p.wait()
    print(mod,p.returncode,round(time.monotonic()-start,3),peak,flush=True)
    if p.returncode: raise SystemExit(1)
    for path in [source,obj/(mod+'.olean')]:
        old_oom = sum(int(l.split()[1]) for l in Path('/sys/fs/cgroup/memory.events').read_text().splitlines() if l.split()[0] in ('oom','oom_kill'))
        with (logs/'digests.txt').open('a') as f:
            f.write(hashlib.sha256(path.read_bytes()).hexdigest()+'  '+str(path)+'\n')
