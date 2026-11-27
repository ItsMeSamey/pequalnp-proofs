"""Original-edge witness repair for supplied switching permutations over GF(3)."""
from collections import defaultdict


def dot(u,v):
    return sum(x*y for x,y in zip(u,v))%3


def sub(u,v):
    return tuple((x-y)%3 for x,y in zip(u,v))


def linear(n,equations):
    """Particular solution and nullspace basis, or None."""
    piv={}
    for row,rhs in equations:
        r=list(row)+[rhs]
        for p,basis in sorted(piv.items()):
            k=r[p]
            r=[(x-k*y)%3 for x,y in zip(r,basis)]
        p=next((i for i in range(n) if r[i]),None)
        if p is None:
            if r[n]:
                return None
        else:
            piv[p]=tuple(x*r[p]%3 for x in r)
    def back(free,hom):
        x=[int(i==free) for i in range(n)]
        for p,row in sorted(piv.items(),reverse=True):
            x[p]=((0 if hom else row[-1])-dot(row[:n],x))%3
        return tuple(x)
    return back(None,False),[back(i,True) for i in range(n) if i not in piv]


class SwitchingQuotient:
    def __init__(self,n,edges,b,generators=(),*,permutations=()):
        if n<0 or b<0:
            raise ValueError('invalid dimensions')
        self.n,self.b=n,b
        self.edges=tuple((u,v,tuple(g)) for u,v,g in edges)
        groups=defaultdict(lambda:defaultdict(list))
        for i,(u,v,g) in enumerate(self.edges):
            if not (0<=u<n and 0<=v<n and u!=v) or len(g)!=b or any(x not in (0,1,2) for x in g):
                raise ValueError('invalid original edge')
            groups[min(u,v),max(u,v)][g].append(i)
        identity=tuple(range(n))
        def permutation(perm):
            perm=tuple(perm)
            if sorted(perm)!=list(identity):
                raise ValueError('invalid vertex permutation')
            return perm
        given=list(generators)
        kernel_done=False
        for perm in permutations:
            perm=permutation(perm)
            eq=[]
            for (u,v),src in groups.items():
                dst=groups.get(tuple(sorted((perm[u],perm[v]))),{})
                if not dst or len(dst)!=len(src):
                    raise ValueError('vertex permutation has no switching lift')
                sample=next(iter(src))
                offsets=[]
                for t in dst:
                    h=sub(t,sample)
                    if all(len(dst.get(tuple((a+c)%3 for a,c in zip(g,h)),()))==len(ids)
                           for g,ids in src.items()):
                        offsets.append(h)
                if not offsets:
                    raise ValueError('vertex permutation has no switching lift')
                offset=offsets[0]
                _,normals=linear(b,((sub(h,offset),0) for h in offsets))
                for normal in normals:
                    row=[0]*(n*b)
                    row[u*b:(u+1)*b]=normal
                    row[v*b:(v+1)*b]=normal
                    eq.append((row,dot(normal,offset)))
            solved=linear(n*b,eq)
            if solved is None:
                raise ValueError('globally inconsistent switch potentials')
            particular,kernel=solved
            def unpack(flat):
                return tuple(flat[j*b:(j+1)*b] for j in range(n))
            given.append((perm,unpack(particular)))
            if not kernel_done:
                given.extend((identity,unpack(k)) for k in kernel)
                kernel_done=True
        self.maps=[]
        self.shifts=[]
        for perm,potential in given:
            perm=permutation(perm)
            p=tuple(tuple(x) for x in potential)
            if len(p)!=n or any(len(row)!=b or any(t not in (0,1,2) for t in row) for row in p):
                raise ValueError('invalid potentials')
            mapping=[None]*len(self.edges)
            for (u,v),source in groups.items():
                dest=groups.get(tuple(sorted((perm[u],perm[v]))),{})
                for g,indices in source.items():
                    h=tuple((x+y+z)%3 for x,y,z in zip(g,p[u],p[v]))
                    dest_ids=dest.get(h,())
                    if len(indices)!=len(dest_ids):
                        raise ValueError('switch fails labelled multiplicities')
                    for i,j in zip(indices,dest_ids):
                        mapping[i]=j
            if sorted(mapping)!=list(range(len(self.edges))):
                raise ValueError('induced edge map is not a permutation')
            self.maps.append(tuple(mapping))
            self.shifts.append(tuple(sum(row[j] for row in p)%3 for j in range(b)))
        _,self.normals=linear(b,((v,0) for v in self.shifts))
        self.rank=b-len(self.normals)
        self.quotient_edges=tuple((u,v,self.project(g)) for u,v,g in self.edges)

    def project(self,g):
        g=tuple(g)
        if len(g)!=self.b or any(x not in (0,1,2) for x in g):
            raise ValueError('invalid label vector')
        return tuple(dot(v,g) for v in self.normals)

    def matching_gain(self,ids):
        if any(type(i) is not int or not 0<=i<len(self.edges) for i in ids) or sorted(
                v for i in ids for v in self.edges[i][:2])!=list(range(self.n)):
            raise ValueError('invalid original matching IDs')
        return tuple(sum(self.edges[i][2][j] for i in ids)%3 for j in range(self.b))

    def repair(self,ids,target):
        ids=tuple(ids)
        target=tuple(target)
        self.project(target)
        delta=sub(target,self.matching_gain(ids))
        solved=linear(len(self.maps),((tuple(g[j] for g in self.shifts),x) for j,x in enumerate(delta)))
        if solved is None:
            raise ValueError('matching lies outside target orbit')
        for mapping,count in zip(self.maps,solved[0]):
            for _ in range(count):
                ids=tuple(mapping[i] for i in ids)
        if self.matching_gain(ids)!=target:
            raise ArithmeticError('original target replay failed')
        return ids


prepare=SwitchingQuotient


def solve(n,edges,target,generators=(),*,permutations=(),backend=None):
    if backend is None:
        from labelled_konig_deficiency import solve as backend
    target=tuple(target)
    q=prepare(n,edges,len(target),generators,permutations=permutations)
    status,ids,metrics=backend(n,q.quotient_edges,q.project(target))
    return status,q.repair(ids,target) if status=='SAT' else None,dict(rank=q.rank,backend=metrics)
