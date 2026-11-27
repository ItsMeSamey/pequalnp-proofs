"""Seven selectors, four full roots, exactly two distinct nonprimitive activations."""
from pathlib import Path
from single_paid import walk,F,halves
from forest3 import forests

def action(x,j,k):
    if j==k:
        d=1<<j
        return ((x&halves[j])>>d)|((x&(F^halves[j]))<<d)
    if j>k:j,k=k,j
    up=halves[j]&(F^halves[k]);down=halves[k]&(F^halves[j]);d=(1<<k)-(1<<j)
    return (x&~(up|down))|((x&up)<<d)|((x&down)>>d)

def options(prefix,exclude=()):
    primitive={u&m for i,u in enumerate(prefix) for m in (halves[i],F^halves[i])}
    closure={0}
    for b in primitive:closure.update({v|b for v in closure})
    keys=[(j,k) for j in range(len(prefix)) for k in range(j,len(prefix))
          if all(action(u,j,k)==prefix[k if i==j else j if i==k else i] for i,u in enumerate(prefix))
          and all(action(u,j,k)==u for u in exclude)]
    seen=set()
    for v in sorted(closure-primitive-{0,F}-set(exclude)):
        if v in seen:continue
        seen.add(v);stack=[v]
        while stack:
            x=stack.pop()
            for j,k in keys:
                y=action(x,j,k)
                if y not in seen:seen.add(y);stack.append(y)
        yield v

def templates():
    for n0 in (4,5):
        for n1 in range(1,7-n0):
            n2=7-n0-n1
            for a in forests(n0):
                if len(a)!=4:continue
                for b in forests(n1):
                    for c in forests(n2):yield a,b,c
def generate():
    rows=set()
    for roots,first,last in templates():
        pre=walk(roots,[F]*4,0)
        for u in options(pre):
            middle=pre+walk(first,[u]*len(first),len(pre))
            for v in options(middle,[u]):
                row=middle+walk(last,[v]*len(last),len(middle))
                primitive={x&m for i,x in enumerate(row) for m in (halves[i],F^halves[i])}
                assert set(row)-primitive-{F}=={u,v}
                rows.add(tuple(row))
    return sorted(rows)
if __name__=='__main__':
    rows=generate()
    Path('two-paid.tsv').write_text(''.join(' '.join(map(str,row))+'\n' for row in rows))
    print('shapes',len(list(templates())),'profiles',len(rows))
