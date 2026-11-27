from fractions import Fraction
from itertools import product
from native_joint_guards import assemble,evaluate,solve
from native_sat_guards import clause_guard,encode,solve_sat
from native_paired_rows import prepare
from check_native_defect import det
from check_native_cut_dp import joins

def direct(guards):
    sizes={};opened=[]
    for p,q,r,s in guards:
        opts=prepare(p,[m for _,m in q],r,s)
        for label,m in q:sizes[label]=len(m)
        if opts:opened.append((q,opts))
    total=0;number=0
    for word in product(*(range(s)for s in sizes.values())):
        state=dict(zip(sizes,word));value=1
        for q,opt in opened:
            rows=[v for j,(label,_) in enumerate(q)for v in opt[j][state[label]][1]]
            value*=abs(det(rows))
        total+=value;number+=1
    return Fraction(total,number)

def run():
    samples=[[],[[1]],[[1],[-1]],[[1,2],[-1,3]],[[1],[-1,2],[-2]],
             [[1,2],[-1,-2]],[[1,1],[-1,2]],[[1,-1],[2,-3]],
             [[1,2,3]],[[1,2,3],[-1,2]],[[1],[-1,2],[2]]]
    for f in samples:
        g,_=encode(f);system=assemble(g);value,t=evaluate(system,{})
        assert value==direct(g),(f,value,direct(g))
        w=solve(g);assert (w is not None)==bool(value)
        if w is not None:
            assert all(joins(p,[q[w[i]] for i,q in m],r,s)for p,m,r,s in g)
        assert (solve_sat(f) is not None)==bool(value)
        for i,group in system[0].items():
            for j in range(len(group[0][1])):
                _,tj=evaluate(system,{i:j},measure=True)
                assert tj is None or tj<=t
    assert solve_sat([[]]) is None
    for k in range(1,5):
        p,m,r,s=clause_guard(range(k),[1]*k)
        assert all(joins(p,[q[v]for (_,q),v in zip(m,w)],r,s)==any(w)for w in product(range(2),repeat=k))
    print('11 correlated exact sums, all recovered assignments, first-level support bounds and clause controls passed')

if __name__=='__main__':run()
