from itertools import combinations
from rank7_missing import main,kernel
from frontier import basis
from wedge_path import wedge
def exhaustive():
    actual,known,extra=main()
    r=12
    forms=[]
    for z in actual:
        row=[0]*r
        for j in range(r):
            for i in range(j):
                if z>>(j*(j-1)//2+i)&1:
                    row[i]^=1<<j;row[j]^=1<<i
        forms.append(row)
    generated=known
    selected=[]
    for weight in range(1,r+1):
        for indices in combinations(range(r),weight):
            a=sum(1<<i for i in indices)
            evaluated=[]
            for row in forms:
                val=0
                for i in indices: val^=row[i]
                evaluated.append(val)
            for b in kernel(evaluated,r):
                candidate=wedge(a,b)
                new=basis(generated+(candidate,))
                if len(new)>len(generated): selected.append((a,b));generated=new
    rest=next(z for z in extra if len(basis(generated+(z,)))>len(generated))
    matrix=[0]*r
    for j in range(r):
        for i in range(j):
            if rest>>(j*(j-1)//2+i)&1:matrix[i]^=1<<j;matrix[j]^=1<<i
    print('all 4095 projections: rank-two span',len(generated),'additional pairs',selected)
    print('missing representative',rest,'alternating rank',len(basis(matrix)))
    return generated,rest
if __name__=='__main__': exhaustive()
