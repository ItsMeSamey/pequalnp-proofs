"""Backward two-state gate peeling; bit 0 is the constant coefficient."""


def reduce_form(word, rows):
    for pivot in sorted(rows, reverse=True):
        if word >> pivot & 1:
            word ^= rows[pivot]
    return word


def restrict(rows, equation):
    value = reduce_form(equation, rows)
    if value < 2:
        return None if value else rows
    return rows | {value.bit_length()-1:value}


def product(a,b):
    if a < 2:
        return b if a else 0
    if b < 2:
        return a if b else 0
    if (a ^ b) < 2:
        return a if a == b else 0
    return None


def peel(n,gates,output):
    """Return disjoint accepting affine systems, or None when unsupported."""
    if n < 0 or output < 0 or output.bit_length() > n+len(gates)+1:
        raise ValueError("invalid output")
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or (a|b).bit_length()>n+j+1:
            raise ValueError("invalid operand")
    flats = []
    rows = {}
    raw = (1<<(n+1))-1
    def emit(domain, response):
        acc = restrict(domain,response^1)
        if acc is not None:
            flats.append(acc)
    while output & ~raw:
        site = output.bit_length()-1
        rest = output ^ (1<<site)
        a,b = (reduce_form(t,rows) for t in gates[site-n-1])
        direct = product(a,b)
        if direct is not None:
            output = reduce_form(rest ^ direct,rows)
            continue
        for form in (a,b,a^b):
            if form < 2 or form & ~raw:
                continue
            branches=[]
            for value in (0,1):
                domain = restrict(rows,form^value)
                term = product(reduce_form(a,domain),reduce_form(b,domain))
                assert term is not None
                response = reduce_form(rest^term,domain)
                branches.append((domain,response))
            if all(f & ~raw for _,f in branches):
                continue
            for domain,f in branches:
                if not f & ~raw:
                    emit(domain,f)
            remaining = [(d,f) for d,f in branches if f & ~raw]
            if not remaining:
                return flats
            rows,output = remaining[0]
            break
        else:
            return None
    emit(rows,output)
    return flats


def intersect_witness(left,right):
    for a in left:
        for b in right:
            rows = a
            for eq in b.values():
                rows = restrict(rows,eq)
                if rows is None:
                    break
            if rows is not None:
                word = 1
                for pivot in sorted(rows):
                    if (word & rows[pivot]).bit_count() & 1:
                        word |= 1<<pivot
                return word>>1
    return None
