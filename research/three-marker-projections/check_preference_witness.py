from itertools import product
from native_preference_witness import solve,compile_binary,top
from native_sat_guards import encode
from check_native_cut_dp import joins

def good(guards,w):
    return all(joins(p,[q[w[i]] for i,q in m],r,s)for p,m,r,s in guards)

def run():
    passed=0
    p=(0,3,4,2,1,5)
    for signs in product((0,1),repeat=4):
        g=[]
        for j in range(2):
            g.append((p,[(i,(a,1-a))for i,a in enumerate(signs[2*j:2*j+2])],1,2))
        want=any(good(g,dict(enumerate(w)))for w in product((0,1),repeat=2))
        w=solve(g);assert (w is not None)==want and (w is None or good(g,w))
        passed+=1
    for f in ([[1]],[[1],[-1]],[[1,2],[-1,3]],[[-1,-2],[1,-3]]):
        g,_=encode(f);w=solve(g)
        labels=sorted(compile_binary(g)[0])
        truth=any(good(g,dict(zip(labels,z)))for z in product(range(2),repeat=len(labels)))
        assert (w is not None)==truth and (w is None or good(g,w))
        passed+=1
    print(passed,'shared-controller nearest-witness comparisons passed')

if __name__=='__main__':run()
