from pathlib import Path
target=43333
expected={(9-p-t,t,f) for f in range(256)
          if (f&15).bit_count()>=3 and (f>>4).bit_count()>=3
          for p in [(f&136).bit_count()] for t in range(10-p)
          if 9-p-t>=f.bit_count()-1}
seen=set()
def check_trace(lines,goal,length):
    known={15,240,3840,4369,8738,17476}
    assert len(lines)==length
    for line in lines:
        a,op,b,eq,y=line.split()
        a,b,y=map(int,(a,b,y))
        assert a in known and (op=='!' or b in known) and eq=='='
        assert y==({'!':65535^a,'&':a&b,'|':a|b}[op])
        known.add(y)
    assert y==goal
p=Path('pilot.log').read_text().splitlines()
for line in p:
    token=line.split()
    if token[0]=='43333' and token[4]=='UNSAT':
        seen.add(tuple(map(int,token[1:4])))
assert seen==expected and len(seen)==75
assert not any(l.startswith('43333 ') and ' SAT ' in l for l in p[:-11])
check_trace(p[-10:],43333,10)
q=Path('neighbor9.log').read_text().splitlines()
check_trace(q[1:],43269,9)
assert (43269^43333).bit_count()==1
Path('keys.tsv').write_text('binary\tnot\tflagmask\tresult\n'+''.join(f'{b}\t{t}\t{f}\tUNSAT\n' for b,t,f in sorted(seen)))
print('75 exact weighted keys and 2 positive DAG traces verified')
