from itertools import product
from affine_boundary_conflict import find_conflict,replay_conflict


def forbid(variables,bits):
    return tuple(-v if b else v for v,b in zip(variables,bits))


def parity_chain(s,last,private_start):
    """p_0=0, p_{i+1}=p_i XOR x_i, p_s=last."""
    p = list(range(private_start,private_start+s+1))
    clauses = [(-p[0],)]
    for i in range(s):
        for a,b,c in product((0,1),repeat=3):
            if a^b!=c:
                clauses.append(forbid((p[i],i+1,p[i+1]),(a,b,c)))
    clauses.append((p[-1] if last else -p[-1],))
    return clauses


def main():
    for s in (1,3,8,32,96):
        for a,b in product((0,1),repeat=2):
            left,right=parity_chain(s,a,s+1),parity_chain(s,b,2*s+2)
            proof=find_conflict(left,right,range(1,s+1))
            assert (proof is not None)==(a!=b)
            if proof is not None:
                assert replay_conflict(left,right,proof)
                assert len(proof[0])==len(proof[1])==4*s+2
                assert not replay_conflict(left,right,(proof[0][1:],proof[1]))
                # Direct source semantics for a few deterministic words, including private bits.
                for assignment in [0,(1<<(3*s+2))-1,0xAAAAAAAA,0x1357]:
                    violated=lambda c: all(bool((assignment>>(abs(l)-1))&1)==(l<0) for l in c)
                    assert sum(violated(cs[j]) for cs,indices in zip((left,right),proof)
                               for j in indices)%2==1
        print("boundary width",s,"source clauses per side",4*s+2)
    variables=(1,2,3)
    low,high=[],[]
    for word in product((0,1),repeat=3):
        (low if sum(word)<=1 else high).append(forbid(variables,word))
    assert find_conflict(low,high,variables) is None
    assert find_conflict([(1,-1)],[],[1]) is None
    assert replay_conflict([()],[],find_conflict([()],[],[]))
    print("undetected nonlinear contradiction and degenerate clauses checked")


if __name__=='__main__':
    main()
