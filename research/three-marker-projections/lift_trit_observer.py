"""Expand two ternary input rotations, then retain the optional physical sockets."""
from itertools import product
stages=[(0,1,2),(0,1,2),(3,4,5),(3,4,5),None,
        (2,7,3),(0,7,3),(0,5,6),(0,3,6)]
feedback=(5,7,4,2,6,1,3,0)
ids={s:i for i,s in enumerate(k for k,r in enumerate(stages)if r is not None)}
def next_gate(stage,track):
    while True:
        s=stages[stage]
        if s is None:
            track=feedback[track]
        elif track in s:
            return 3*ids[stage]+s.index(track)
        stage=(stage+1)%len(stages)
wiring=[next_gate((s+1)%len(stages),track) for s,ports in enumerate(stages)
        if ports is not None for track in ports]
roots=[next_gate(0,track) for track in (6,7)]
assert sorted(wiring)==list(range(24))
print(roots,wiring)
truth=0;counts=[]
for x in range(16):
    count=0
    for aux in range(16):
        word=x+(aux<<4); site=roots[0]
        while True:
            gate,pos=divmod(site,3)
            site=wiring[3*gate+(pos+((word>>gate)&1))%3]
            if site==roots[1]:count+=1;break
            if site==roots[0]:break
    counts.append(count)
    if count:truth|=1<<x
assert truth==0x1669
print(hex(truth),counts)
