"""Rooted row membership with paired sections and a supplied binary split tree."""
from itertools import product
from random import Random

def span(vectors):
    values={0}
    for v in vectors:
        if v not in values:
            values |= {x^v for x in values}
    return values

def split(gates):
    if len(gates)==1: return gates[0]
    m=len(gates)//2
    return split(gates[:m]),split(gates[m:])

def apply(rows,y):
    return sum(((v&y).bit_count()%2)<<i for i,v in enumerate(rows))

def solve(rows,c,twist,tree):
    """Rows are symmetric bit masks; gate g ties indices 2*g and 2*g+1."""
    allbits=(1<<len(rows))-1
    def visit(node):
        if isinstance(node,int):
            mask=3<<(2*node)
        else:
            left,lt=visit(node[0]);right,rt=visit(node[1]);mask=left|right
            left_outputs={key[1] for key in lt};right_outputs={key[1] for key in rt}
        outside=allbits^mask
        incoming=span(row&mask for i,row in enumerate(rows) if outside>>i&1)
        table={}
        for incoming_mask in incoming:
            if isinstance(node,int):
                for toggle,y0 in product(range(2),range(4)):
                    selected=(twist&mask) ^ (mask if toggle else 0)
                    y=y0<<(2*node)
                    if y&~selected:continue
                    ay=apply(rows,y)
                    if (c^incoming_mask^ay)&selected:continue
                    table[incoming_mask,ay&outside]=selected,y
            else:
                # Outgoing interface masks remain in full matrix coordinates.
                for lo in left_outputs:
                    for ro in right_outputs:
                        a=lt.get(((incoming_mask^ro)&left,lo))
                        b=rt.get(((incoming_mask^lo)&right,ro))
                        if a is not None and b is not None:
                            table[incoming_mask,(lo^ro)&outside]=(a[0]|b[0],a[1]|b[1])
        return mask,table
    return visit(tree)[1].get((0,0))

def check():
    rng=Random(2027)
    for test in range(360):
        m=1+test%5;n=2*m
        rows=[0]*n
        for i in range(n):
            for j in range(i):
                if rng.randrange(2):rows[i]|=1<<j;rows[j]|=1<<i
        c=rng.randrange(1<<n);t=rng.randrange(1<<n)
        choices=[t ^ sum((3<<(2*i)) for i in range(m) if s>>i&1)
                 for s in range(1<<m)]
        truth=any((c&x) in span(rows[i]&x for i in range(n) if x>>i&1)
                  for x in choices)
        order=list(range(m));rng.shuffle(order)
        result=solve(rows,c,t,split(order))
        assert (result is not None)==truth
        if result is not None:
            x,y=result
            assert x in choices and y&~x==0 and (c^apply(rows,y))&x==0
    print('360 rooted cut-rank decisions and witnesses passed')
if __name__=='__main__':check()
