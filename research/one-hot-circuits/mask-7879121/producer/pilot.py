import subprocess
import sys
exe='/dev/shm/official-7879121-register'
def run(mask,b,t,flags):
    data=subprocess.check_output([exe,str(mask),str(b),str(t),str(flags)],text=True)
    print(data,end='',flush=True)
    return ' UNSAT ' not in data
assert run(15|4369,1,0,17)
assert not run(15^4369,1,0,17)
assert not run(43333,7,2,119)
for flags in range(256):
    if (flags&15).bit_count()<3 or (flags>>4).bit_count()<3: continue
    paid=(flags&136).bit_count()
    for t in range(10-paid):
        b=9-paid-t
        if b>=flags.bit_count()-1:run(43333,b,t,flags)
print('ALL NEGATIVE MODES COMPLETED',flush=True)
assert run(43333,9,1,119)
