"""Target-specific flat projection and source-edge repair for supplied affine actions."""
from collections import deque
from labelled_switching_generators import dot,linear,sub


def add(a,b):
    return tuple((x+y)%3 for x,y in zip(a,b))


class AffineOrbits:
    def __init__(self,n,edges,b,actions,*,trusted=False,semantic_certificate=None):
        self.n,self.b=n,b
        self.edges=tuple((u,v,tuple(g)) for u,v,g in edges)
        def valid(g):
            return len(g)==b and all(x in (0,1,2) for x in g)
        if n<0 or b<0 or any(not(0<=u<n and 0<=v<n and u!=v) or not valid(g) for u,v,g in self.edges):
            raise ValueError('invalid dimensions or labelled edge')
        self.actions=[]
        for action in actions:
            if len(action)==3:
                A,t,emap=action
                vertex=None
            elif len(action)==5:
                A,t,vertex,emap,p=action
                vertex=tuple(vertex)
                p=tuple(tuple(g) for g in p)
                if sorted(vertex)!=list(range(n)) or len(p)!=n or any(not valid(g) for g in p):
                    raise ValueError('invalid vertex certificate')
            else:
                raise ValueError('invalid action')
            A,t,emap=tuple(tuple(row) for row in A),tuple(t),tuple(emap)
            if len(A)!=b or any(not valid(row) for row in A) or not valid(t) or sorted(emap)!=list(range(len(self.edges))):
                raise ValueError('invalid affine action or edge permutation')
            if linear(b,((row,0) for row in A))[1]:
                raise ValueError('singular linear part')
            if vertex is not None:
                if tuple(sum(row[j] for row in p)%3 for j in range(b))!=t:
                    raise ValueError('translation differs from vertex-potential sum')
                for i,(u,v,g) in enumerate(self.edges):
                    x,y,h=self.edges[emap[i]]
                    if {x,y}!={vertex[u],vertex[v]} or h!=add(tuple(dot(row,g) for row in A),add(p[u],p[v])):
                        raise ValueError('invalid edgewise affine certificate')
            else:
                for i,(u,v,g) in enumerate(self.edges):
                    x,y,_=self.edges[emap[i]]
                    for j in range(i):
                        a,c,_=self.edges[j]
                        r,s,_=self.edges[emap[j]]
                        if {u,v}.isdisjoint((a,c)) and not {x,y}.isdisjoint((r,s)):
                            raise ValueError('edge permutation does not preserve disjointness')
                if semantic_certificate is not None:
                    if not semantic_certificate(n,self.edges,A,t,emap):
                        raise ValueError('semantic certificate rejected')
                elif not trusted:
                    raise ValueError('compact action needs a certified semantic gain identity')
            inv=[None]*len(emap)
            for i,j in enumerate(emap):
                inv[j]=i
            self.actions.append((A,t,emap,tuple(inv)))

    def orbit(self,target):
        target=tuple(target)
        if len(target)!=self.b or any(x not in (0,1,2) for x in target):
            raise ValueError('invalid target')
        pred={target:None}
        todo=deque([target])
        while todo:
            g=todo.popleft()
            for j,(A,t,_,_) in enumerate(self.actions):
                h=add(tuple(dot(row,g) for row in A),t)
                if h not in pred:
                    pred[h]=(g,j)
                    todo.append(h)
        return pred

    def gain(self,ids):
        if any(type(i) is not int or not 0<=i<len(self.edges) for i in ids) or sorted(
                v for i in ids for v in self.edges[i][:2])!=list(range(self.n)):
            raise ValueError('invalid original matching edge IDs')
        return tuple(sum(self.edges[i][2][j] for i in ids)%3 for j in range(self.b))

    def repair(self,ids,target,pred=None):
        target=tuple(target)
        pred=self.orbit(target) if pred is None else pred
        ids=tuple(ids)
        g=self.gain(ids)
        if g not in pred:
            raise ValueError('source matching gain is outside target orbit')
        while pred[g] is not None:
            g,j=pred[g]
            inv=self.actions[j][3]
            ids=tuple(inv[i] for i in ids)
        if self.gain(ids)!=target:
            raise ArithmeticError('invalid repaired original witness')
        return ids

    def flat(self,target,pred=None):
        target=tuple(target)
        pred=self.orbit(target) if pred is None else pred
        allowed={sub(g,target) for g in pred}
        zero=(0,)*self.b
        spaces={frozenset((zero,)):()}
        best=()
        for v in sorted(allowed):
            for U,basis in tuple(spaces.items()):
                if v in U:
                    continue
                larger=U|{add(x,v) for x in U}|{sub(x,v) for x in U}
                if larger<=allowed and larger not in spaces:
                    new=basis+(v,)
                    if len(new)>len(best):
                        best=new
                    if len(larger)*3>len(allowed):
                        # The next possible flat size already exceeds the orbit size.
                        return new
                    spaces[larger]=new
        return best


prepare=AffineOrbits


def solve(n,edges,target,actions,*,trusted=False,semantic_certificate=None,backend=None,avoid=None):
    """avoid(n,edges,forbidden_scalar_tuple) -> status, witness IDs, metrics."""
    target=tuple(target)
    q=prepare(n,edges,len(target),actions,trusted=trusted,semantic_certificate=semantic_certificate)
    pred=q.orbit(target)
    if q.b==1 and len(pred)==2 and avoid is not None:
        forbidden=next((v,) for v in range(3) if (v,) not in pred)
        status,ids,metrics=avoid(n,q.edges,forbidden)
        stats=dict(orbit=2,mode='avoid',backend=metrics)
    else:
        if backend is None:
            from labelled_konig_deficiency import solve as backend
        U=q.flat(target,pred)
        _,normals=linear(q.b,((u,0) for u in U))
        def proj(g):
            return tuple(dot(v,g) for v in normals)
        projected=tuple((u,v,proj(g)) for u,v,g in q.edges)
        status,ids,metrics=backend(n,projected,proj(target))
        stats=dict(orbit=len(pred),flat_rank=len(U),mode='quotient',backend=metrics)
        if status=='SAT' and proj(q.gain(tuple(ids)))!=proj(target):
            raise ArithmeticError('backend returned a wrong quotient matching')
    return status,q.repair(ids,target,pred) if status=='SAT' else None,stats
