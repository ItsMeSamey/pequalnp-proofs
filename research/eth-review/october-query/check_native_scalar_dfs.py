"""Independent finite source-kernel oracle. The evaluated DFS is the only producer import."""
from fractions import Fraction
from hashlib import sha256
from itertools import product
from math import prod
from pathlib import Path
import sys
sys.dont_write_bytecode = True
source = Path('/workspace/scratch/eth-october-primary')
sys.path.insert(0, str(source))
from scalar_group_dfs import evaluate

def residue(x, modulus):
    x = Fraction(x)
    assert x.denominator % 2
    return x.numerator * pow(x.denominator, -1, modulus) % modulus

def verify(a, i, t, z, P, sparse, group_count):
    L, step, modulus = 2**a, 2**(i+1), 2**P
    T = t + 2*L*z
    nodes = range(-L,L)
    deriv = prod(-k for k in nodes if k)
    numerator = prod(T-k for k in nodes)
    pref = Fraction(numerator, deriv*T)
    first = residue(pref, modulus)
    ratio = residue(Fraction(step,T),modulus)
    w_at = lambda d: residue(Fraction(prod(T-k for k in nodes if k!=d),deriv),modulus)
    assert first == w_at(0)
    high = (P+1)//2 - 1
    bs = sorted({0,high}) if sparse else list(range(P-1))
    # Endpoints embed the two leaf-side packets and an ancestor crossing packet.
    q = group_count//4
    packets = [(0,q,False),(2*q,3*q,True),(0,2*q,False)]
    modes = [(s,g,b+1,1) for s,g,_ in packets for b in bs]
    child_vars = [[] for _ in range(group_count)]
    pieces = []
    for j,(s,g,positive) in enumerate(packets):
        start=j*len(bs)
        child_vars[s].append((j,True))
        child_vars[g].append((j,False))
        pieces.append([(first*pow(ratio,b,modulus))%modulus for b in bs])
    sign = lambda positive: 1 if positive else -1
    # Literal reference enumerates active row choices, independently of the DFS,
    # as a flat product of at most (P+1)^3 triples. Multi-selections have zero
    # target coefficient because there is only one active row per packet.
    legal,extra,negative = 0,0,False
    for picks in product([None]+list(range(len(bs))),repeat=len(packets)):
        weight=[0 if k is None else bs[k]+1 for k in picks]
        value=1
        for j,k in enumerate(picks):
            positive=packets[j][2]
            if k is None:
                value *= 0 if positive else 2
            else:
                value *= sign(positive)*pieces[j][k]*(2 if bs[k]==0 else 1)
                negative |= not positive and pieces[j][k]!=0
        if sum(weight)<P:
            legal=(legal+value)%modulus
        elif weight[0]+weight[2]<P and weight[1]+weight[2]<P:
            assert value%modulus==0
            extra+=1
    assert negative and extra
    # Nonzero target factors that annihilate only on multiplication across halves.
    h=bs.index(high)
    assert pieces[0][h] and pieces[1][h] and 2*(high+1)>=P
    assert (pieces[0][h]*pieces[1][h])%modulus==0
    if not sparse:
        # Original deformed parent, directly contracting the two equal source bits.
        # The neutral second row contributes ell_0+ell_1=1.
        v=(w_at(0)+w_at(step))%modulus
        direct=prod(v if positive else 2-v for _,_,positive in packets)%modulus
        assert legal==direct
    def leaf(g,beta):
        # Charge only producer-implementation result slots separately from this
        # on-demand independent O(incident modes)-time physical-factor assembly.
        on_path=(0,2) if g<group_count//2 else (1,2)
        assert sum(modes[j][2]*beta[j] for m in on_path
                   for j in range(m*len(bs),(m+1)*len(bs)))<P
        val=1
        for j,is_source in child_vars[g]:
            ks=[k for k in range(len(bs)) if beta[j*len(bs)+k]]
            positive=packets[j][2]
            if is_source:
                val*=2 if not ks else (2 if bs.index(0) in ks else 1)
            elif len(ks)>1:
                return 0
            elif ks:
                val*=sign(positive)*pieces[j][ks[0]]
            else:
                val*=int(not positive)
        return val%modulus
    R=(0,1,lambda x,y:(x+y)%modulus,lambda x,y:(x*y)%modulus)
    scalar,work=evaluate(range(group_count),modes,P,leaf,R)
    assert scalar==legal
    assert work.adds==work.muls and work.peak<=2*group_count.bit_length()-1
    if P<20:
        histogram,hwork=evaluate(range(group_count),modes,P,leaf,R,'histogram')
        assert sum(histogram)%modulus==legal and hwork.peak>work.peak
    return extra,work.leaf_calls,work.peak

if __name__=='__main__':
    for name in ('scalar_group_dfs.py','check_scalar_group_dfs.py'):
        print(sha256((source/name).read_bytes()).hexdigest(),name)
    for a,i in [(2,0),(4,0),(4,1)]:
        for z in [-1,1]:
            # Shell-specific real formula for P_i with M=6 and p=3, two live
            # slots per packet; sparse series clamps all other mode exponents.
            u=a//2
            exact=3+8*((3*6+u-1)//u)*(2**(a-i))+8*6*(a+1)
            for P,sparse,n in [(2*(a+2-i),False,4),(exact,True,4)]:
                print(a,i,z,P,sparse,n,verify(a,i,-(2**i),z,P,sparse,n))
    print('64', verify(2,0,-1,1,8,True,64))
