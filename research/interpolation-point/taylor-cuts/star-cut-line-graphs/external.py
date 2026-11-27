"""Exact external-interface tables for a supplied binary cut-rank decomposition."""
def span(columns):
    basis={}
    for col in columns:
        while col:
            pivot=col.bit_length()-1
            if pivot not in basis:
                basis[pivot]=col
                break
            col^=basis[pivot]
    out=[0]
    for col in basis.values():out += [s^col for s in out]
    return out

def external_table(adj,labels,forced,p,tree):
    n=len(adj); full=(1<<n)-1
    if not n:return {0:0}
    def visit(node):
        if isinstance(node,int):
            i=node; bit=1<<i
            rows={}
            for shift in ([0,bit] if adj[i] else [0]):
                if not (forced&bit): rows[shift,0,0]=0
                if (shift!=0)==bool((labels[i]&p).bit_count()%2):
                    rows[shift,adj[i],labels[i]]=bit
            return bit,rows
        l,lt=visit(node[0]); r,rt=visit(node[1])
        region=l|r; exterior=full^region
        shifts=span(adj[i]&region for i in range(n) if exterior>>i&1)
        out={}
        for b in shifts:
            for (bl,cl,gl),zl in lt.items():
                for (br,cr,gr),zr in rt.items():
                    if bl==((b^cr)&l) and br==((b^cl)&r):
                        out[b,(cl^cr)&exterior,gl^gr]=zl|zr
        return region,out
    region,result=visit(tree)
    assert region==full
    return {g:z for (b,c,g),z in result.items() if not b and not c}
