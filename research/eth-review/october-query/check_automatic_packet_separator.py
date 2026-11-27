from automatic_packet_separator import recognize,execute
from itertools import product

opts=dict(r=2,a=1,u=1,delta=8,slot_cap=256,order_state_cap=512,strict=False)
f=[(1,2),(-2,3),(3,1)]
def run(n,rows,cap,width,**other):
    return recognize(n,rows,placement_cap=cap,width_cap=width,**dict(opts,**other))
seed=run(3,f,1,8)
better=execute(3,f,placement_cap=10,width_cap=5,work_cap=10**12,witness=True,**opts)
assert seed['profile']['width']==6 and better['profile']['width']==5
assert better['stats']['placements']>1 and seed['packets']!=better['packets']
q=better['readout']
assert q['status']=='exact' and q['max_enum_width']==5
assert q['work_bound']==better['profile']['executor_price']
assert q['count']==sum(all(any(bool(w & (1<<(abs(l)-1)))==(l>0) for l in c) for c in f) for w in range(8))
assert run(3,f,1,5)['status']=='unknown'
assert run(1,[(1,)],10,0)['status']=='no_in_template'
assert run(1,[(1,)],10,0,order_state_cap=0)['status']=='unknown'
assert run(1,[(1,)],0,0)['status']=='unknown'
assert run(1,[(1,)],5,5,pins=((0,1),),slot_cap=0)['status']=='unknown'
pinned=execute(3,f,placement_cap=1,width_cap=8,work_cap=10**12,witness=True,pins=((0,1),),**opts)
assert pinned['readout']['count']<=q['count']
print('PASS: actual 6-to-5 layout improvement, port-pinned readout, exhaustive scoped NO and cap refusals')
