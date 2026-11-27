"""Encode width-three CNF using shared data proxies for original variables."""
from compiler import xor_equivalence


def compile_proxy(n, clauses, *, pin_selectors=False):
    rows = [tuple(row) for row in clauses]
    if type(n) is not int or n < 0 or any(
        len(row) > 3 or any(type(x) is not int or not 1 <= abs(x) <= n for x in row)
        for row in rows
    ):
        raise ValueError("invalid width-three formula")
    if n == 0:
        return 0, ([()] if rows else []), []
    blocks = [[(0, -i, -i), (1, i, i)] for i in range(1, n + 1)]
    for row in rows:
        if len(row) == 3:
            guard, left, right = row
            blocks[abs(guard) - 1].append((int(guard < 0), left, right))
    count = 0
    output = []
    selectors = []
    proxy = {}
    for groups in blocks:
        p, q, r = range(count + 1, count + 4)
        selectors.append((p, q, r))
        count += 3
        if pin_selectors:
            output.extend([(-p,), (-q,)])
        for j in range(max(3, len(groups))):
            a, b, e, f, g, c = range(count + 1, count + 7)
            count += 6
            for triple in ((a,p,e), (b,q,f), (e,r,g), (g,f,c)):
                output.extend(xor_equivalence(*triple))
            if j == len(groups):
                output.extend([(a,), (-b,), (a,b,c)])
                continue
            trigger, left, right = groups[j]
            output.append((a, b, -c if trigger else c))
            for site, literal in ((a, left), (b, right)):
                signed_site = site if literal > 0 else -site
                key = abs(literal)
                if key in proxy:
                    root = proxy[key]
                    output.extend([(-signed_site,root), (signed_site,-root)])
                else:
                    proxy[key] = signed_site
    for row in rows:
        if len(row) < 3:
            output.append(tuple(proxy[abs(x)] if x > 0 else -proxy[abs(x)] for x in row))
    return count, output, selectors
