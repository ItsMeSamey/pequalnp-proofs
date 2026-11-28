from itertools import product
from check_remote_pivot_source import oracle
from source_remote_pivot_reach import solve

def check(rows,pins=()):
    ref=oracle(rows,pins)
    r=solve(1009,rows,source_pins=pins)
    assert r['status']==('UNSAT' if ref is None else 'SAT'),r
    t=r['true_variables']
    if ref is None: assert t is None
    else:
        assert tuple(sorted(set(t)))==t
        assert all((x in t)==b for x,b in pins)
        assert all(any((abs(l) in t)==(l>0) for l in row) for row in rows)
    assert r['metrics']['projection_calls']<=1+3*sum(len(row)==3 for row in rows)
    return r

def main():
    source=[(-1,2),(-2,3),(-3,1),(1,4),(-4,-1),(-2,-4)]
    for mask in range(64):
        binary=[b for j,b in enumerate(source) if mask>>j&1]
        triples=[(1,-2,3),(-1,2,4),(1,3,-4)]
        if mask%3==0: triples.append((-1,-3,4))
        for pins in ((),((4,mask&1),)): check(binary+triples,pins)
    w,u,v=11,13,15
    rows=[(-w,u),(w,v),(19,21),(19,-21)]
    for a,b,c in ((1,2,3),(4,5,6),(7,8,9)):
        rows.extend(((-u,-a),(-v,-b),(a,b,c),(-a,-b,-c)))
    assert tuple(check(rows)['pivots'])==(w,)
    for y in (0,1): check(rows,[(w,y)])
    no=rows+[(s,t*2,h*3) for s,t,h in product((1,-1),repeat=3)]
    assert check(no)['status']=='UNSAT'
    for cap in ('branch_cap','discovery_cap'):
        ans=solve(1009,rows,**{cap:0})
        assert ans['status']=='UNKNOWN' and ans['reason']==cap.replace('_',' ')
    print('128 signed binary backgrounds/pins; shared length-two paths, disconnected backbone, UNSAT and call bounds passed')
if __name__=='__main__': main()
