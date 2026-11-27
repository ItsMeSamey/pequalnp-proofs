"""Find a joining physical mask on a supplied binary leaf tree of gate indices."""
from itertools import product
from math import gcd

def wedge_feature(response, cut, r, s):
    positions={v:i for i,v in enumerate(cut) if v!=r}
    coefficients={0:1}
    for wire, dest in sorted(response.items()):
        if wire==s:
            continue
        row={}
        if wire!=r:
            row[positions[wire]]=2
        if dest!=r:
            j=positions[dest]
            row[j]=row.get(j,0)-1
        new={}
        for subset, val in coefficients.items():
            for j,a in row.items():
                if not a or subset>>j&1:
                    continue
                sign=-1 if (subset>>(j+1)).bit_count()%2 else 1
                k=subset|1<<j
                new[k]=new.get(k,0)+sign*a*val
        coefficients={k:v for k,v in new.items() if v}
    return coefficients

def independent(row, basis):
    while row:
        i=min(row)
        if i not in basis:
            basis[i]=row
            return True
        b=basis[i]
        a=row[i];c=b[i]
        row={j:c*row.get(j,0)-a*b.get(j,0) for j in row.keys()|b.keys()}
        row={j:v for j,v in row.items() if v}
        g=gcd(*row.values()) if row else 1
        if g>1:
            row={j:v//g for j,v in row.items()}
    return False

def solve(feedback, menus, r, s, tree):
    """Three-input sites in consecutive triples, feedback[exit]=next entrance.

    A menu lists allowed cyclic shifts (e.g. (0,1) or one fixed value).
    Marks r and s are entrance wires. Returns actual shifts or None.
    """
    n=len(menus);N=3*n
    if sorted(feedback)!=list(range(N)) or not (0<=r<N and 0<=s<N):
        raise ValueError('invalid feedback or root wire')
    if any(not m or any(v not in (0,1,2) for v in m) for m in menus):
        raise ValueError('empty or invalid rotation menu')
    order=[];labels=[];pending=[(tree,False)]
    while pending:
        t,done=pending.pop()
        if type(t) is int:
            labels.append(t);order.append(t)
        elif done:
            order.append(None)
        else:
            if not isinstance(t,(list,tuple)) or len(t)!=2:
                raise ValueError('expected a binary leaf tree')
            pending.extend([(t,True),(t[1],False),(t[0],False)])
    if sorted(labels)!=list(range(n)):
        raise ValueError('tree must cover all gates exactly once')
    if r==s:return tuple(m[0] for m in menus)
    tail=[0]*N
    for j,v in enumerate(feedback):tail[v]=j//3
    partial=[]
    for t in order:
        if t is not None:
            gates={t}
            def candidates():
                for v in menus[t]:
                    response={i:feedback[3*t+(i%3+v)%3] for i in range(3*t,3*t+3)}
                    yield response,{t:v}
        else:
            gb,right=partial.pop();ga,left=partial.pop();gates=ga|gb
            def candidates():
                for (l,wl),(h,wh) in product(left,right):
                    yield l|h,wl|wh
        cut=sorted({r,s}|{i for i in range(N) if (i//3 in gates)!=(tail[i] in gates)})
        boundary=set(cut)
        basis={};states=[]
        for steps,witness in candidates():
            response={}
            for i in cut:
                if i//3 not in gates:
                    continue
                j=steps[i]
                while j not in boundary:j=steps[j]
                response[i]=j
            if independent(wedge_feature(response,cut,r,s),basis):
                states.append((response,witness))
        partial.append((gates,states))
    _,states=partial.pop()
    if not states:return None
    return tuple(states[0][1][j] for j in range(n))
