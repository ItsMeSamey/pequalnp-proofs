"""Exact degree-d Boolean policy peeling for packed independent-control pencils.

Policies are used only to identify the constant part of the pointwise column image:
they do not restrict x in the counted source. Every monomial is squarefree.
"""
from itertools import combinations
from controlled_image_peeling import exact as finish, specialization
from controlled_witness_radius import column_basis, row_equations
from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def monomials(n,d):
    return [sum(1<<j for j in S) for size in range(min(n,d)+1)
            for S in combinations(range(n),size)]


def policy_constants(m,n,U,forms,degree):
    """Basis of constants attainable by sum_i u_i q_i times degree-bounded p_i."""
    if degree<0:
        raise ValueError("negative policy degree")
    powers=monomials(n,degree+1)
    slots={mask:i for i,mask in enumerate(powers)}
    policies=monomials(n,degree)
    equations={}
    constants={}
    for col,(linear,c) in zip(U,forms):
        if not col:
            continue
        terms=[1<<j for j in range(n) if linear>>j&1]
        for s in policies:
            packed=(col<<(m*slots[s])) if c else 0
            for bit in terms:
                packed ^= col<<(m*slots[s|bit])
            higher=packed>>m
            value=packed&((1<<m)-1)
            residue,carry=reduce_vector(higher,equations)
            if residue:
                equations[residue.bit_length()-1]=residue,carry^value
            else:
                insert(carry^value,0,constants)
    return constants


def exact(m,A,b,U,forms,degree,*,terminal="auto"):
    A,U,forms=tuple(A),tuple(U),tuple(forms)
    if m<0 or degree<0 or len(U)!=len(forms) or any(not 0<=v<1<<m for v in (*A,b,*U)):
        raise ValueError("invalid degree or pencil dimensions")
    if any(not 0<=v<1<<len(A) or c not in (0,1) for v,c in forms):
        raise ValueError("invalid affine form")
    if terminal not in ("auto","character","brute"):
        raise ValueError("invalid terminal")
    original=m,A,b,U,forms
    offset=0
    transform=[1<<j for j in range(len(A))]
    stats={"rounds":[],"signed_exponent":0,"terminal":None}
    while True:
        n,k=len(A),len(U)
        image=column_basis(U)
        residues=[reduce_vector(v,image)[0] for v in (*A,b)]
        flat=affine_domain(n,row_equations(residues[:-1],residues[-1],m))
        if flat is None:
            return 0,None,stats
        origin,dirs,_=flat
        if len(dirs)<n:
            offset ^= apply_basis(transform,origin)
            transform=[apply_basis(transform,d) for d in dirs]
            b ^= apply_basis(A,origin)
            A=tuple(apply_basis(A,d) for d in dirs)
            forms=tuple((sum(parity(v&d)<<j for j,d in enumerate(dirs)),c^parity(v&origin))
                        for v,c in forms)
        const=policy_constants(m,len(A),U,forms,degree)
        def project(v):
            return reduce_vector(v,const)[0]
        kept={}
        new_cols=[]
        new_forms=[]
        for col,(v,c) in zip(U,forms):
            u=project(col)
            packed=(u if c else 0)
            for j in range(len(A)):
                if v>>j&1:
                    packed |= u<<(m*(j+1))
            if insert(packed,0,kept):
                new_cols.append(u)
                new_forms.append((v,c))
        delta=k-len(const)-len(kept)
        stats["signed_exponent"]+=delta
        stats["rounds"].append((n,k,len(A),len(const),len(kept),delta))
        U,forms=tuple(new_cols),tuple(new_forms)
        A=tuple(project(v) for v in A)
        b=project(b)
        if not const and k==len(U) and n==len(A):
            break
    reduced,witness,stats["terminal"]=finish(m,A,b,U,forms,terminal=terminal)
    exponent=stats["signed_exponent"]
    if exponent<0:
        count,rem=divmod(reduced,1<<(-exponent))
        if rem:
            raise AssertionError("nonintegral source count")
    else:
        count=reduced<<exponent
    if witness is None:
        return count,None,stats
    y=offset^apply_basis(transform,witness[1])
    ways,x=specialization(*original,y)
    if not ways:
        raise AssertionError("source witness lift failed")
    return count,(x,y),stats
