"""Exhaustive two-by-two assignment audit over all ternary label-set masks."""
from itertools import product


def add(a,b):
    return sum(1<<z for z in range(3) if any(a>>x&1 and b>>((z-x)%3)&1 for x in range(3)))


def main():
    plus=[[add(x,y) for y in range(8)] for x in range(8)]
    checks=0
    for mandatory,a,b,c,d in product(range(8),repeat=5):
        opts=((mandatory,a,d),(mandatory,b,c))
        actual=0
        for q,x,y in opts:
            actual|=plus[plus[q][x]][y]
        rigid=0
        by_single={}
        full=False
        for assignment in ((0,3),(1,2)):
            tokens=((-1,mandatory),)+tuple((i,(a,b,c,d)[i]) for i in assignment)
            if any(not x for _,x in tokens):
                continue
            flex=[(i,x) for i,x in tokens if x.bit_count()>1]
            if len(flex)>=2:
                full=True
                break
            complement=1
            for _,x in tokens:
                if x.bit_count()==1:
                    complement=plus[complement][x]
            if not flex:
                rigid|=complement
            else:
                key=flex[0]
                by_single[key]=by_single.get(key,0)|complement
        predicted=7 if full else rigid
        if not full:
            for (_,x),other in by_single.items():
                predicted|=7 if other.bit_count()>=2 else plus[x][other]
        assert predicted==actual
        checks+=1
    print(checks,"exhaustive scalar slot systems passed")


if __name__=="__main__":
    main()
