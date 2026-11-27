"""Full-support ternary kernel search with local weight-four rows and global labels."""
from itertools import combinations,product
from secrets import randbelow
from ternary_labelled_matching import search


def partition(rows,b,h):
    supports=[tuple(i for i,a in enumerate(row) if a) for row in rows]
    mandatory={j for j,s in enumerate(supports) if len(s)!=4}
    def visit(globals_,marked):
        if len(globals_)>b or len(marked)>h:
            return None
        incidence={}
        for j,s in enumerate(supports):
            if j not in globals_:
                for i in s:
                    if i not in marked:
                        incidence.setdefault(i,[]).append(j)
        for i,rs in incidence.items():
            if len(rs)>2:
                for g,m in [(globals_,marked|{i})]+[(globals_|{j},marked) for j in rs[:3]]:
                    found=visit(g,m)
                    if found is not None:
                        return found
                return None
        return sorted(globals_),sorted(marked)
    return visit(mandatory,set())


def gadget(n,rows,global_ids,fixed):
    """Return a labelled matching instance and slope decoding data, or None for invalid quota."""
    cols=[i for i in range(n) if i not in fixed]
    global_set=set(global_ids)
    ports={i:[] for i in cols}
    baseline=dict(fixed)
    edges=[]
    tags={}
    size=0
    zero=(0,)*len(global_ids)
    def vertex():
        nonlocal size
        size+=1
        return size-1
    def edge(a,b,tag=None):
        if tag is None:
            edges.append((a,b,zero))
        else:
            tags[len(edges)]=tag
            edges.append((a,b,tuple(-2*baseline[tag]*rows[j][tag]%3 for j in global_ids)))
    total_quota=0
    for j,row in enumerate(rows):
        if j in global_set:
            continue
        quota=2-sum(row[i]*v%3==1 for i,v in fixed.items())
        local=[]
        for i in cols:
            if row[i]:
                a=vertex()
                ports[i].append((a,row[i]))
                local.append(a)
        if not 0<=quota<=len(local):
            return None
        total_quota+=quota
        for _ in range(len(local)-quota):
            dummy=vertex()
            for a in local:
                edge(dummy,a)
    singles=[]
    opposite=0
    for i,occ in ports.items():
        baseline[i]=(-occ[0][1] if occ else -1)%3
        if not occ:
            a,b,c,d=(vertex() for _ in range(4))
            edge(a,b,i); edge(b,c); edge(c,d); edge(d,a)
        elif len(occ)==1:
            singles.append((occ[0][0],i))
        else:
            (a,s),(b,t)=occ
            if s==t:
                edge(a,b,i)
            else:
                opposite+=1
                center=vertex()
                edge(a,center,i)
                edge(b,center)
    k=len(singles)
    reservoir=[vertex() for _ in range(k+((total_quota-opposite-k)%2))]
    for a,i in singles:
        for v in reservoir:
            edge(a,v,i)
    for a,b in combinations(reservoir,2):
        edge(a,b)
    target=tuple(-sum(row[i]*baseline[i] for i in range(n))%3 for row in (rows[j] for j in global_ids))
    return size,edges,target,baseline,tags


def solve(n,rows,*,b,h,rounds=1,randbelow_fn=randbelow):
    """Return SAT with a tuple of nonzero trits, otherwise UNKNOWN."""
    if any(type(x) is not int or x<0 for x in (n,b,h)):
        raise ValueError("invalid dimension or parameter")
    rows=[tuple(a%3 for a in row) for row in rows]
    if any(len(row)!=n for row in rows):
        raise ValueError("wrong width")
    parts=partition(rows,b,h)
    if parts is None:
        return "UNKNOWN",None
    globals_,marked=parts
    for signs in product((1,2),repeat=len(marked)):
        built=gadget(n,rows,globals_,dict(zip(marked,signs)))
        if built is None:
            continue
        size,edges,target,baseline,tags=built
        status,match=search(size,edges,target,rounds=rounds,randbelow_fn=randbelow_fn)
        if status=="SAT":
            for e in match:
                if e in tags:
                    i=tags[e]
                    baseline[i]=-baseline[i]%3
            x=tuple(baseline[i] for i in range(n))
            if any(sum(a*s for a,s in zip(row,x))%3 for row in rows):
                raise ArithmeticError("invalid original-column witness")
            return "SAT",x
    return "UNKNOWN",None
