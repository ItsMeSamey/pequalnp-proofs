"""Test the actual equality-pair scalar kernel on small signed-definite cuts."""
from fractions import Fraction as F
from itertools import product
from random import Random

def check(dim, sign, seed):
    rng=Random(seed)
    # A guaranteed definite symmetric integer matrix, perturbed and shifted.
    q=[[rng.randrange(-2,3) for _ in range(dim)] for _ in range(dim)]
    mat=[[sign*(sum(q[i][k]*q[j][k] for k in range(dim))+(i==j))
          for j in range(dim)] for i in range(dim)]
    offset=[F(rng.randrange(-3,4),3) for _ in range(dim)]
    ports=[[offset[i]+sum(y*bit for y,bit in zip(mat[i],x)) for i in range(dim)]
           for x in product((0,1),repeat=dim)]
    # A further unselected port factor must preserve definiteness.
    for v in ports:
        v.append(sum(v)/3)
    scores=[]
    for a in ports:
        row=[]
        for b in ports:
            val=1
            for u,v in zip(a,b):
                val*=(1-u+u*v)*(1-v+u*v)
            row.append(val)
        scores.append(row)
    # Positive Schur complements certify every leading principal minor exactly.
    for i in range(len(scores)):
        pivot=scores[i][i]
        assert pivot>0,(seed,i)
        for j in range(i+1,len(scores)):
            ratio=scores[j][i]/pivot
            for k in range(i+1,len(scores)):
                scores[j][k]-=ratio*scores[i][k]

if __name__=='__main__':
    for seed in range(16):
        check(2+seed%3,(-1)**seed,seed)
    print('16 fixed equality-pair Gram kernels have full Boolean-cube rank and positive exact Schur pivots.')
