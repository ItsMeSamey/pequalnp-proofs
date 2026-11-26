"""Exhaust every conjunction/injection truth table on the required private-triple restrictions."""
from itertools import combinations, permutations
def close(bank):
    # Any finite subset conjunction, including both Boolean constants.
    result={0,allbits}
    for b in bank:result|={x&b for x in result.copy()}
    return result
def possible(edges,extra):
    global allbits
    labels=edges+extra
    jobs=[(i,) for i in range(len(labels))]+list(combinations(range(len(labels)),2))
    allbits=(1<<len(jobs))-1
    def truth(pred):return sum(int(pred(j))<<k for k,j in enumerate(jobs))
    pure=[truth(lambda a:any(labels[i]>>p&1 for i in a)) for p in range(3)]
    target=truth(lambda a:len(a)==2)
    ext=[truth(lambda a:i in a) for i in range(len(edges),len(labels))]
    def visit(pool,todo):
        terms=close(pool)
        if not todo:
            return any((f|(pure[2]&p))==target for f in terms for p in terms)
        return any(visit(pool+[todo[0]|a],todo[1:]) for a in terms)
    return any(visit(pure[:2],list(order)) for order in permutations(ext))
if __name__=='__main__':
    for edges,extra in [((3,5,6),(1,)),((5,6),(1,1)),((3,5),(1,))]:
        assert not possible(edges,extra)
        print(edges,extra,'excluded')
