"""Exact counting and witness for controlled pencils after peeling constant maps.

Packed columns follow controlled_witness_radius.search. A round restricts the data
to the affine rhs-membership flat and removes constants in the span of the
vector-valued affine maps, including constants created by cancellations.
"""
from controlled_witness_radius import ProjectedOracle, column_basis, row_equations
from quadratic_target import affine_domain, apply_basis, insert, parity, reduce_vector


def specialization(m,A,b,U,q,y):
    rows={}
    for i,(col,(v,c)) in enumerate(zip(U,q)):
        if parity(v&y)^c:
            insert(col,1<<i,rows)
    residual,x=reduce_vector(b^apply_basis(A,y),rows)
    return (0,None) if residual else (1<<(len(U)-len(rows)),x)


def exact(m,A,b,U,activators,*,terminal="auto"):
    """Return exact count, optional (original controls, original data), and statistics."""
    A,U,q=tuple(A),tuple(U),tuple(activators)
    if terminal not in ("auto","brute","character"):
        raise ValueError("invalid terminal choice")
    if m<0 or len(U)!=len(q) or any(not 0<=v<1<<m for v in (*A,b,*U)):
        raise ValueError("invalid output dimensions")
    if any(not 0<=v<1<<len(A) or c not in (0,1) for v,c in q):
        raise ValueError("invalid activator")
    original=(m,A,b,U,q)
    data_origin=0
    data_basis=[1<<j for j in range(len(A))]
    exponent=0
    stats={"rounds":[],"terminal":None,"terminal_exponent":0,"multiplicity_exponent":0}
    while True:
        n,k=len(A),len(U)
        output_basis=column_basis(U)
        residues=[reduce_vector(v,output_basis)[0] for v in (*A,b)]
        flat=affine_domain(n,row_equations(residues[:-1],residues[-1],m))
        if flat is None:
            return 0,None,stats
        point,dirs,_=flat
        if len(dirs)<n:
            # All changes on the right use the pre-restriction coordinates.
            data_origin ^= apply_basis(data_basis,point)
            data_basis=[apply_basis(data_basis,v) for v in dirs]
            b ^= apply_basis(A,point)
            A=tuple(apply_basis(A,v) for v in dirs)
            q=tuple((sum(parity(mask&v)<<j for j,v in enumerate(dirs)), c^parity(mask&point))
                    for mask,c in q)
        # Row-reduce linear parts while tracking their constants as output vectors.
        # Each dependency of a new map on prior linear parts supplies one
        # generator of the constant subspace; zero dependencies are harmless.
        linear_rows={}
        constants={}
        for col,(mask,c) in zip(U,q):
            linear=sum(col<<(j*m) for j in range(len(A)) if mask>>j&1)
            residue,carry=reduce_vector(linear,linear_rows)
            value=(col if c else 0)^carry
            if residue:
                linear_rows[residue.bit_length()-1]=residue,value
            else:
                insert(value,0,constants)

        def project(v):
            return reduce_vector(v,constants)[0]
        rows={}
        next_U=[]
        next_q=[]
        for col,(mask,c) in zip(U,q):
            u=project(col)
            # Distinguish the constant block from every linear coefficient block.
            map_value=(u if c else 0)
            for j in range(len(A)):
                if mask>>j&1:
                    map_value |= u<<((j+1)*m)
            if insert(map_value,0,rows):
                next_U.append(u)
                next_q.append((mask,c))
        advance=k-len(constants)-len(next_U)
        if advance<0:
            raise AssertionError("invalid projected control dimension")
        exponent+=advance
        stats["multiplicity_exponent"]=exponent
        stats["rounds"].append((n,k,len(A),len(constants),len(next_U),advance))
        A=tuple(map(project,A))
        b=project(b)
        U,q=tuple(next_U),tuple(next_q)
        if n==len(A) and k==len(U):
            break

    rank=len(column_basis(U))
    mode=("brute" if len(A)<=rank else "character") if terminal=="auto" else terminal
    stats["terminal"]=mode
    stats["terminal_exponent"]=len(A) if mode=="brute" else rank
    witness_y=None
    if mode=="brute":
        count=0
        for y in range(1<<len(A)):
            ways,_=specialization(m,A,b,U,q,y)
            count+=ways
            if ways and witness_y is None:
                witness_y=y
    else:
        oracle=ProjectedOracle(m,A,b,U,q,{},())
        count=oracle.count()
        if count:
            witness_y=oracle.witness_y()
    if not count:
        return 0,None,stats
    y=data_origin^apply_basis(data_basis,witness_y)
    ways,x=specialization(*original,y)
    if not ways:
        raise AssertionError("terminal witness failed original control lift")
    return count<<exponent,(x,y),stats
