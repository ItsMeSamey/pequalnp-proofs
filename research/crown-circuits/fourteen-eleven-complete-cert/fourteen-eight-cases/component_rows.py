"""Exact connected-component degree multisets before physical gate decorations."""
import csv
import sys
from itertools import product
from degree_rows import graphical

def components():
    types=[]
    for es in range(1,15):
        for n2,n3,n4 in product(range(es+1),range(2*es//3+1),range(es//2+1)):
            n1=2*es-2*n2-3*n3-4*n4
            if n1<0:
                continue
            row=(n1,n2,n3,n4)
            q=sum(row)
            if not 2<=q<=es+1:
                continue
            ds=[d for d,count in enumerate(row,1) for _ in range(count)]
            if graphical(ds):
                types.append((es,row))
    return types

def partitions(types,start,budget,prefix=()):
    if budget==0:
        yield prefix
        return
    for i in range(start,len(types)):
        edges,ds=types[i]
        if edges>budget:
            break
        yield from partitions(types,i,budget-edges,prefix+(ds,))

def records():
    for parts in partitions(components(),0,14):
        n1,n2,n3,n4=map(sum,zip(*parts))
        if n3+n4==0 or n2+n3+n4<2 or (len(parts)==1 and n4):
            continue
        yield (sum((n1,n2,n3,n4)),len(parts),n1,n2,n3,n4,
               ';'.join(','.join(map(str,p)) for p in parts))

if __name__=='__main__':
    writer=csv.writer(sys.stdout,delimiter='\t',lineterminator='\n')
    writer.writerow(('vertices','components','degree1','degree2','degree3','degree4','component_degree_counts'))
    writer.writerows(records())
