from itertools import product
N=161203
cases=[]
for a,b in product(range(31),repeat=2):
    deleted=(a+b)*403-a*(a-1)//2-b*(b-1)//2
    survivors=2*N-deleted
    degree=402-max(a,b)
    cases.append((646425-4*N+1+2*survivors//(degree+1)+a+b,a,b))
assert max(cases)==(3310,30,0)
print('961 early independent-pin count bounds passed')
