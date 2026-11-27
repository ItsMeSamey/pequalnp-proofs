"""Process supervisor for serial Lean. Linux proc values are in KiB."""
from pathlib import Path as P
import subprocess,time,tempfile
def compile_guarded(lean,args,cwd,env):
 cg=P('/sys/fs/cgroup')
 def stats(p):
  return {a.rstrip(':'):int(b) for a,b,*_ in (line.split() for line in p.read_text().splitlines() if len(line.split())>1 and line.split()[1].isdigit())}
 def events():
  val=stats(cg/'memory.events');return val['oom']+val['oom_kill']
 def safe(mem):
  return mem['anon']+mem['shmem']+mem['kernel']<=7247757312 and not (int((cg/'memory.current').read_text())>8455716864 and mem['file']-mem['shmem']<805306368)
 assert safe(stats(cg/'memory.stat')),'guard rejected launch'
 start=time.monotonic();old=events();peak=0
 with tempfile.TemporaryFile(mode='w+t') as out:
  q=subprocess.Popen([lean,'-j1',*args],env=env,cwd=cwd,stdout=out,stderr=subprocess.STDOUT)
  while q.poll() is None:
   try:
    pp=P('/proc',str(q.pid));r=stats(pp/'smaps_rollup');rss=stats(pp/'status').get('VmRSS',0)
    anon=r.get('Pss_Anon',0);peak=max(peak,anon)
    if (rss>3145728 or peak>563200 or (rss>2621440 and 100*r.get('Pss_File',0)<65*rss) or time.monotonic()-start>25 or events()>old or not safe(stats(cg/'memory.stat'))):q.kill()
   except (FileNotFoundError,ProcessLookupError):pass
   time.sleep(.12)
  out.seek(0);log=out.read();assert q.returncode==0,(args,q.returncode,peak,log)
 return log
