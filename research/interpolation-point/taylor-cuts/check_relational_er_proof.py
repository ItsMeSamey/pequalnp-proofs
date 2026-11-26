from itertools import combinations,product
from relational_er_proof import translate,verify,_definitions


def holds(clause,word):
    return any(bool(word & (1<<(abs(x)-1)))==(x>0) for x in clause)


def main():
    source=[(1,),(-1,)]
    steps=[("ext",2,"not",(1,)),("res",0,2,1),("res",3,1,1),("res",5,4,2),("end",6)]
    # (-y,-x), (y,x), then -y and y, then the empty clause.
    proof=translate(1,source,steps)
    assert verify(1,source,proof)
    for bad in [proof[:-1],proof+[("end",6)], [("ext",1,"not",(1,)),*proof[1:]],
                [("ext",2,"not",(2,)),*proof[1:]], [proof[0],("bit",4,2,1,(-2,),(2,)),*proof[2:]],
                [proof[0],("bit",0,2,1,(-2,),(-2,)),*proof[2:]], [*proof[:-1],("end",0)]]:
        assert not verify(1,source,bad)
    for op,args in [("and",(1,-2)),("or",(1,-2)),("not",(-1,))]:
        cs=_definitions(op,3,args)
        for mask in range(4):
            v=[holds((a,),mask) for a in args]
            expected=all(v) if op=="and" else any(v) if op=="or" else not v[0]
            assert [b for b in (0,1) if all(holds(c,mask|(b<<2)) for c in cs)]==[int(expected)]
    universe=[(1,),(-1,),(2,),(-2,),*product((1,-1),(2,-2))]
    for choice in range(1<<len(universe)):
        source=[c for i,c in enumerate(universe) if choice>>i&1]
        rows=[tuple(sorted(c)) for c in source]
        steps=[]
        for i,a in enumerate(rows):
            for j,b in enumerate(rows[:i]):
                for l,r,left,right in [(i,j,a,b),(j,i,b,a)]:
                    for v in (1,2):
                        if v not in left or -v not in right:
                            continue
                        c=tuple(sorted((set(left)-{v})|(set(right)-{-v})))
                        if c not in rows and not any(-x in c for x in c):
                            rows.append(c)
                            steps.append(("res",l,r,v))
        unsat=not any(all(holds(c,m) for c in source) for m in range(4))
        if () in rows:
            steps.append(("end",rows.index(())))
        assert verify(2,source,translate(2,source,steps))==unsat
    print("256 complete two-variable CNFs verified against brute force, all three extensions and tamper controls passed")


if __name__=="__main__":
    main()
