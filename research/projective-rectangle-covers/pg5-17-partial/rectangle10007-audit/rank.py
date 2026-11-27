"""Exact scalar consequences of trace and closure census for the 31×31 matrix."""
from fractions import Fraction as F
from math import ceil
from pathlib import Path

def main():
    lines=(Path(__file__).resolve().parent/'spectrum.txt').read_text().splitlines()
    spectrum=[tuple(map(int,line.split())) for line in lines[:-1]]
    assert max(a*b for a,b,_ in spectrum)==60
    assert sum(n for a,b,n in spectrum if a*b==60)==6200
    sizes={j: max(a for a,b,_ in spectrum if b>=j) for j in range(1,26)}
    minimum=[(F(0),())]
    for m in range(1,26):
        minimum.append(min((minimum[m-j][0]+F(1,sizes[j]),minimum[m-j][1]+(j,)) for j in range(1,m+1)))
    assert minimum[-1][0]==F(14,33)
    for k in range(13,20):
        candidates=[]
        for A in range(775,60*k+1):
            floor=ceil(((F(1,k)+F(4,31))*A*A/125-775-3*(A-775))/2)
            candidates.append((floor,A))
        T=min(n for n,_ in candidates)
        assert T=={13:107,14:81,15:60,16:42,17:27,18:14,19:1}[k]
        print(k, T)
    assert F(125*9,8*775)-F(4,31)==F(13,248)
    assert ceil(F(248,13))==20
    assert 28*F(8,13)>17

if __name__=='__main__':
    main()
