from cold8 import *
s,t=1,2|16|32
u=V^s^t
H=sum(1<<x for x in range(1024) if x&1 and x&t)
K0=sum(1<<x for x in range(1024) if any((x&e)==e and not(e&1) for e in E))
K1=K0|sum(1<<x for x in range(1024) if x&48)
assert (K0&(ALL^H)|K1&H)==F
M=next(m for m in MIS if (H>>m)&1)
hp,hn,p0,n0,p1,n1=tables(s,t,u,M)
for knownpos,knownneg,truth in [(hp,hn,H),(p0,n0,K0),(p1,n1,K1)]:
 assert not knownpos&~truth and not knownneg&truth
assert conflict([(LS[1]^ALL,LS[1])],7)==[]
andxy=(ALL^LS[1])&(ALL^LS[2]);orxy=(ALL^LS[1])|(ALL^LS[2])
assert conflict([(andxy,ALL^andxy),(orxy,ALL^orxy)],3)==[3]
print('Actual graph composition control passed across all 1024 assignments; LCA positive and negative controls passed; unsafe MIS',M)
