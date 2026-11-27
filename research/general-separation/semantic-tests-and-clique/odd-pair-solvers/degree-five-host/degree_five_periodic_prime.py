"""Finite radius-six primeness certificate for the four-site periodic relay."""
from itertools import combinations
from odd_pair_square_multiplicity_check import supports


def chain(periods):
    rows=[4,8,1,2]
    s,t=0,1
    for _ in range(periods):
        c=len(rows)
        p,s_new,t_new=c+1,c+2,c+3
        rows.extend([0]*4)
        for i,j in ((s,t),(c,s),(c,t),(c,p),(p,s),(p,s_new),(s,t_new)):
            assert not rows[i]>>j&1
            rows[i]|=1<<j
            rows[j]|=1<<i
        s,t=s_new,t_new
    return rows,s,t


def sites(s):
    while s:
        bit=s&-s
        yield bit.bit_length()-1
        s^=bit


def certificate(rows):
    unit=(1<<len(rows))-1
    pending=1
    reached=1
    while pending:
        ne=0
        for i in sites(pending):
            ne|=rows[i]
        pending=ne&~reached
        reached|=pending
    assert reached==unit
    hist=[0]*5
    failed=[]
    for i,j in combinations(range(len(rows)),2):
        if not (rows[i]>>j&1 or rows[i]&rows[j]):
            continue
        current=(1<<i)|(1<<j)
        for step in range(1,5):
            add=0
            for v in sites(current):
                add|=rows[i]^rows[v]
            nxt=current|add
            if nxt==current:
                failed.append((i,j,current))
                break
            current=nxt
            if current.bit_count()>5:
                hist[step]+=1
                break
        else:
            raise AssertionError('four strict expansions must reach six sites')
    return hist,failed


def main():
    total=[0]*5
    for m in range(1,15):
        rows,p,q=chain(m)
        assert sum(r.bit_count()==5 for r in rows)==m and max(r.bit_count() for r in rows)==5
        assert all(r.bit_count()%2 for r in rows)
        assert rows[p].bit_count()==rows[q].bit_count()==1
        assert all(abs(i//4-j//4)<=1 for i,r in enumerate(rows) for j in sites(r))
        counts,failed=certificate(rows)
        assert failed==([(2,7,132)] if m==1 else [])
        if m>=2:
            total=[x+y for x,y in zip(total,counts)]
        if m<=4:
            assert list(supports(rows,(1<<p)|(1<<q)))==[(1<<len(rows))-1]
    print('m=2..14 closure thresholds by round',total[1:],
          'final 14-period distribution',counts[1:])


if __name__=='__main__':
    main()
