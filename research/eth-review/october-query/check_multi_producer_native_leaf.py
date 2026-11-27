from check_multi_producer_cnf import violations
from multi_producer_parity import compile_system
from multi_producer_native_leaf import count


if __name__=='__main__':
    for n,clauses in [(3,[(-1,-2),(-1,-3)]),(2,[(1,),(-1,)]),(3,[(-1,-2),(1,)])]:
        rows=violations(clauses)
        terms=sorted(set().union(*rows)-{0})
        net=compile_system(n,rows,0,[(0,),(1,)],[terms[::2],terms[1::2]])
        expected=sum(all(any(bool(x>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses) for x in range(1<<n))
        got=count(net)
        assert got==expected,(clauses,got,expected)
        print(n,net.wires,got)
    print('three original connected CNFs matched true native leaf, including shared variable and UNSAT')
