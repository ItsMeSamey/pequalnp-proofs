import fcntl,hashlib,os,resource,subprocess,time
from pathlib import Path
D=Path('/dev/shm/team04-relaxed170-wide')
checker=Path('/workspace/scratch/syn_pruning/bank11/drat-trim')
cnf=D/'branch-0000.cnf';proof=D/'branch-0000.drat'
for p,h in [(checker,'4ef9e11c06e648f6fed570250bdcb48a161d33121ebce77462db7e5cdefcae1b'),(cnf,'2271f119fd9f1e567feffcb8df46f3721a6deb27bc6cef508f2d94218a2b4c20'),(proof,'56d39cabc195cd38d8c37cbe2c54eb42e4cafce8a7d71bdd3a21cd8f38e9416f')]:
 assert hashlib.sha256(p.read_bytes()).hexdigest()==h
def limits():
 os.nice(15);resource.setrlimit(resource.RLIMIT_CPU,(6,6));resource.setrlimit(resource.RLIMIT_AS,(256*1024**2,)*2)
with open('/workspace/scratch/pnp-native-search.lock','a') as lock:
 try:fcntl.flock(lock,fcntl.LOCK_EX|fcntl.LOCK_NB)
 except BlockingIOError:raise SystemExit(75)
 log=Path('/workspace/scratch/site-team-07/wide04-verifier.log')
 with log.open('wb') as f:
  p=subprocess.Popen([checker,cnf,proof],stdout=f,stderr=subprocess.STDOUT,preexec_fn=limits)
  start=time.monotonic()
  while p.poll() is None:
   try:rss=int(Path(f'/proc/{p.pid}/statm').read_text().split()[1])*os.sysconf('SC_PAGE_SIZE')
   except FileNotFoundError:continue
   if rss>100*1024**2 or time.monotonic()-start>12:p.kill();p.wait();raise RuntimeError('resource guard')
   time.sleep(.01)
 print('exit',p.returncode,'elapsed',time.monotonic()-start,'maxrss_kib',resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss)
 assert p.returncode==0 and b's VERIFIED' in log.read_bytes()
