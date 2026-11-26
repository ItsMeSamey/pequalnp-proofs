"""Signed-CNF relational lemma replay with sequential definitional extensions."""


def _clause(lits,limit):
    raw=tuple(lits)
    if any(type(v) is not int or v==0 or abs(v)>limit for v in raw):
        raise ValueError("literal outside active namespace")
    return tuple(sorted(set(raw)))


def _definitions(op,y,args):
    if op=="not" and len(args)==1:
        x,=args
        return ((-y,-x),(y,x))
    if op=="and" and len(args)==2:
        a,b=args
        return ((-y,a),(-y,b),(y,-a,-b))
    if op=="or" and len(args)==2:
        a,b=args
        return ((y,-a),(y,-b),(-y,a,b))
    raise ValueError("invalid extension operation or arity")


def translate(n,source,steps):
    """Translate indexed resolution/ER records to explicit one-bit interface records.

    Source rows receive IDs 0..m-1. ('ext',y,op,args) appends definitions in
    the order in _definitions. ('res',left,right,pivot) appends a resolvent,
    with left containing +pivot and right containing -pivot. ('end',id) closes.
    """
    if type(n) is not int or n<0:
        raise ValueError("invalid variable count")
    rows=[_clause(c,n) for c in source]
    limit=n
    def get(i):
        if type(i) is not int or not 0<=i<len(rows):
            raise ValueError("unknown predecessor")
        return rows[i]
    result=[]
    for step in steps:
        kind,*data=step
        if kind=="ext":
            y,op,args=data
            args=tuple(args)
            if type(y) is not int or y!=limit+1 or any(type(x) is not int or not 1<=abs(x)<=limit for x in args):
                raise ValueError("extension must be fresh and acyclic")
            limit=y
            rows.extend(_clause(c,limit) for c in _definitions(op,y,args))
            result.append(("ext",y,op,args))
        elif kind=="res":
            left,right,pivot=data
            a,b=get(left),get(right)
            if type(pivot) is not int or pivot<=0 or pivot not in a or -pivot not in b:
                raise ValueError("invalid resolution pivot")
            c=_clause((set(a)-{pivot})|(set(b)-{-pivot}),limit)
            # Complementary pins make a tautological clause vacuously valid.
            result.append(("bit",left,right,pivot,c,tuple(-lit for lit in c)))
            rows.append(c)
        elif kind=="end":
            end,=data
            get(end)
            result.append(("end",end))
        else:
            raise ValueError("unknown record")
    return result


def verify(n,source,proof):
    """Return True only for a closed proof of unsatisfiability of source."""
    try:
        if type(n) is not int or n<0:
            return False
        rows=[_clause(c,n) for c in source]
        limit=n
        finished=False
        for step in proof:
            if finished:
                return False
            kind,*data=step
            if kind=="ext":
                y,op,args=data
                args=tuple(args)
                if type(y) is not int or y!=limit+1 or any(type(x) is not int or not 1<=abs(x)<=limit for x in args):
                    return False
                defs=_definitions(op,y,args)
                limit=y
                rows.extend(_clause(c,limit) for c in defs)
            elif kind=="bit":
                left,right,pivot,claim,pins=data
                if any(type(i) is not int or not 0<=i<len(rows) for i in (left,right)):
                    return False
                if type(pivot) is not int or not 1<=pivot<=limit:
                    return False
                c=_clause(claim,limit)
                pins=tuple(pins)
                if pins!=tuple(-x for x in c):
                    return False
                pos=set(pins)
                if not any(-p in pos for p in pos):
                    # Under all pins, exactly one test bit must force opposite
                    # choices, or a pinned antecedent is already false.
                    def residual(row):
                        return None if any(x in pos for x in row) else {x for x in row if -x not in pos}
                    a,b=residual(rows[left]),residual(rows[right])
                    if a!=set() and b!=set() and (a!={pivot} or b!={-pivot}):
                        return False
                rows.append(c)
            elif kind=="end":
                i,=data
                if type(i) is not int or not 0<=i<len(rows) or rows[i]!=():
                    return False
                finished=True
            else:
                return False
        return finished
    except (TypeError,ValueError):
        return False
