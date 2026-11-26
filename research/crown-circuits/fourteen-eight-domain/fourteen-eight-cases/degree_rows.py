"""Coarse degree-count rows for canonical live raw-incidence graphs."""
import csv
import sys
from itertools import product

def graphical(degrees):
    ds = sorted(degrees, reverse=True)
    return all(sum(ds[:k]) <= k * (k - 1) + sum(min(k, d) for d in ds[k:])
               for k in range(1, len(ds) + 1))

def rows():
    for n2, n3, n4 in product(range(15), range(10), range(8)):
        n1 = 28 - 2*n2 - 3*n3 - 4*n4
        if n1 < 0 or n3 + n4 == 0 or n2 + n3 + n4 < 2:
            continue
        ds = [1]*n1 + [2]*n2 + [3]*n3 + [4]*n4
        if not graphical(ds):
            continue
        q = len(ds)
        for c in range(max(1, q-14), q//2+1):
            if c == 1 and n4:
                continue
            # One component of maximum allowed order and c-1 isolated edges.
            h = q - 2*(c-1)
            if max(ds) >= h or 14 > h*(h-1)//2 + c-1:
                continue
            yield (q, c, n1, n2, n3, n4)

if __name__ == '__main__':
    writer = csv.writer(sys.stdout, delimiter='\t',lineterminator='\n')
    writer.writerow(('vertices','components','degree1','degree2','degree3','degree4'))
    writer.writerows(sorted(rows()))
