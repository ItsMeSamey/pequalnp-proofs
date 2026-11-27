"""Shifted 3×3 even-row/even-column observation code in original signed CNF."""
def fixture():
    ids=tuple(range(1,10))
    rows=[(0,1,2),(3,4,5),(6,7,8)]
    columns=[(0,3,6),(1,4,7),(2,5,8)]
    blocks=rows+columns
    shift=1  # Flip the first cell, hence its row and column syndromes are odd.
    clauses=[]
    for block in blocks:
        rhs=sum((shift>>i)&1 for i in block)%2
        for w in range(8):
            if w.bit_count()%2!=rhs:
                clauses.append(tuple(-(j+1) if w>>i&1 else j+1 for i,j in enumerate(block)))
    clauses.extend(((1,-5,9),(-3,5,-7)))
    return 10,tuple(clauses),ids,tuple(blocks)
