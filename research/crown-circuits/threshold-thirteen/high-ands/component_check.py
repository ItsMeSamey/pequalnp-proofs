from itertools import product
cases=[]
for k,H,p in product(range(4,14),range(1,14),range(1,14)):
    if H<k or p<H or k+3*(H-1)>13:
        continue
    # If p>H some component has at least two vertices; its second vertex adds
    # at least two distinct labels beyond its chosen representative.
    if k+3*(H-1)+2*(p>H)>13:
        continue
    cases.append((k,H,p))
assert cases == [(4,4,4)]
assert not [row for row in cases if row[0]+2<=row[2]]
print('Before the star inequality the only triple (k,H,p) is (4,4,4); after it none remains.')
