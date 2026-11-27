"""Check the two-qubit phase-lifting control using exact integer determinants."""
from itertools import combinations, product

prime = 65537
units = (1, 256, -1, -256)
rays = []
for j in range(4):
    rays.append([int(i == j) for i in range(4)])
for i,j in combinations(range(4),2):
    for phase in units:
        ray = [0]*4
        ray[i],ray[j] = 1,phase
        rays.append(ray)
for a,b,h in product(range(4),range(4),range(2)):
    rays.append([units[(a*x+b*y+2*h*x*y)%4] for x,y in product(range(2),repeat=2)])
target = [5,10,5,6+8*256]
def determinant(a,b,c,rows):
    i,j,k = rows
    return (a[i]*(b[j]*c[k]-b[k]*c[j])-a[j]*(b[i]*c[k]-b[k]*c[i])
            + a[k]*(b[i]*c[j]-b[j]*c[i]))
pairs = sum(all(determinant(a,b,target,rows)%prime==0 for rows in combinations(range(4),3))
            for a,b in combinations(rays,2))
assert len(rays)==60 and pairs==0
print(len(rays),pairs)
