import subprocess,sys
from collections import Counter
from h5_p7_cover_prefix import candidates,CASES
ix=int(sys.argv[1])
i,j=CASES[ix]
source=''.join(' '.join(map(str,(ix,i,j,*q)))+'\n' for q in candidates(ix))
run=subprocess.run([sys.argv[2]],input=source,text=True,check=True,capture_output=True)
counts=Counter(run.stdout.splitlines())
assert sum(counts.values())==source.count('\n')
for key,count in sorted(counts.items()):
    print(key,count)
