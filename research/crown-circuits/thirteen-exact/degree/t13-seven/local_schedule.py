"""Single-star signatures of the unique ordinary OR on its seven nonempty inputs."""
def terms(bank):
    out={0,127}
    for a in bank:out|={a&b for b in list(out)}
    return out
def solve(pos,d=0):
    x=[sum(1<<(v-1) for v in range(1,8) if v>>i&1) for i in range(3)]
    target=sum(1<<(v-1) for v in range(1,8) if v.bit_count()>=2)
    slots=x[d:].copy();slots.insert(pos,None)
    support=set()
    def walk(bank,j,orgate,operands):
        pool=terms(bank)
        if j==len(slots):
            if target in pool:support.add((orgate,tuple(sorted(operands))))
            return
        v=slots[j]
        if v is None:
            for a in pool:
                for b in pool:
                    if a<=b:walk(bank+[a|b],j+1,a|b,(a,b))
        else:
            for z in set(v|w for w in pool):walk(bank+[z],j+1,orgate,operands)
    walk(x[:d],0,None,None);return support
if __name__=='__main__':
    for p in range(4):
        res=solve(p)
        print(p,len(res),sorted(res))

def trace(pos,d=0,pre=False):
    x=[sum(1<<(v-1) for v in range(1,8) if v>>i&1) for i in range(3)]
    target=sum(1<<(v-1) for v in range(1,8) if v.bit_count()>=2)
    slots=x[d:].copy();slots.insert(pos,None);found=set()
    def visit(bank,j,ports,marked):
        pool=terms(bank)
        if j==len(slots):
            if target in pool:found.add((ports,tuple(marked)))
            return
        v=slots[j]
        if v is None:
            for a in pool:
                for b in pool:
                    if a<=b:visit(bank+[a|b],j+1,(a,b),marked)
        else:
            for w in pool:
                z=v|w
                visit(bank+[z],j+1,ports,[*marked,w if pre else z])
    visit(x[:d],0,None,[]);return found
