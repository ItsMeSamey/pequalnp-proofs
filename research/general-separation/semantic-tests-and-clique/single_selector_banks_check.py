"""Compile full map matrices and compare every microstep to gate evaluation."""
from random import Random

def compile_map(w,gates,output):
    L=w+len(gates)+1
    banks=len(gates)+1
    A=[0]*(L*banks)
    B=A.copy()
    sel=0
    for i in range(banks):
        fr=i*L
        to=((i+1)%banks)*L
        bit=lambda j:1<<(fr+j)
        if i==len(gates):
            for j,z in enumerate(output):
                A[to+j]=bit(z)
            A[to+L-1]=bit(L-1)
            continue
        for j in range(L):
            A[to+j]=bit(j)
        op,u,v=gates[i]
        slot=to+w+i
        if op=='&':
            A[slot]=0
            B[slot]=bit(v)
            sel |= bit(u)
        elif op=='^':
            A[slot]=bit(u)^bit(v)
        else:
            A[slot]=bit(L-1)^bit(u)
    return L,A,B,sel

def linear(A,x):
    return sum(((row&x).bit_count()%2)<<j for j,row in enumerate(A))

rng=Random(6001)
steps=0
for _ in range(50):
    w=3
    gates=[(rng.choice('&^~'),rng.randrange(w+i),rng.randrange(w+i)) for i in range(6)]
    output=[rng.randrange(w+6) for j in range(w)]
    L,A,B,sel=compile_map(w,gates,output)
    for x in range(1<<w):
        state=x|(1<<(L-1))
        values=state
        for i in range(len(gates)+1):
            state=linear(A,state)^(((state&sel).bit_count()%2)*linear(B,state))
            if i<len(gates):
                op,u,v=gates[i]
                a,b=(values>>u)&1,(values>>v)&1
                z={'&':a&b,'^':a^b,'~':1^a}[op]
                values|=z<<(w+i)
                expected=values<<((i+1)*L)
            else:
                expected=(1<<(L-1))|sum(((values>>z)&1)<<j for j,z in enumerate(output))
            assert state==expected
            steps+=1
print(steps,'matrix microsteps passed across 50 circuits and all 3-bit inputs')
