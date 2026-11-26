from itertools import product
from check_recognition import points
from solver import basis, reduce_with_trace
for n in range(4):
    width,fixed,edges,extra=points(n)
    for mask in range(1<<len(edges)):
        ordinary=[a|(b<<width) for a,b in fixed+[v for i,v in enumerate(extra) if mask>>i&1]]
        t=1|(1<<width)
        total=0
        for d in range(1,1<<(2*width),2):
            if (d&t).bit_count()%2:
                continue
            rows=basis(x for x in ordinary if not (x&d).bit_count()%2)
            total+=not reduce_with_trace(t,rows)[0]
        colorings=sum(all(x[i]!=x[j] for k,(i,j) in enumerate(edges) if mask>>k&1)
                      for x in product(range(4),repeat=n))
        assert total==(1<<(2*width-2))-colorings
print('Direct eligible-column span counts match each graph through three vertices')
