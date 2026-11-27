from pathlib import Path
from random import Random
random=Random(790761);count=0
for line in Path(__file__).with_name('t8-two-profiles.tsv').read_text().splitlines():
 w,q=map(int,line.split())
 for mask in [0,4095,768,3072]+[random.randrange(4096) for _ in range(12)]:
  states=[bool(mask>>j&1) for j in range(12)]
  for j,target in ((4,w),(5,q)):
   if states[2*j] and states[2*j+1]:
    for k in range(12):states[k]|=bool(target>>k&1)
  accepted=any(states[2*j] and states[2*j+1] for j in range(4))
  cert=0
  for z in range(64):
   b=sum(1<<(2*j+((z>>j)&1)) for j in range(4))
   if q&b:b|=1<<(10+((z>>5)&1))
   if w&b:b|=1<<(8+((z>>4)&1))
   cert+=not(mask&b)
  assert bool(cert)!=accepted
  count+=1
print('checked',count,'mask/profile pairs against all 64 backward certificates')
