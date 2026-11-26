"""Single-exponential unseeded DP using one boundary vector and one covector."""
from solve import augment, canonical, functional, image, intersection, solve


def restrictions(space, sub):
    return tuple(solve(space,v) for v in sub)


def project_value(coeff, inclusion):
    return sum(((coeff & v).bit_count()%2)<<i for i,v in enumerate(inclusion))


def state_table(ordinary, roots, layout=None):
    def balanced(lo,hi):
        if lo==hi:
            return None
        if hi==lo+1:
            return lo
        mid=(lo+hi)//2
        return (balanced(lo,mid),balanced(mid,hi))

    def prepare(tree):
        if tree is None:
            return (),None,None
        if isinstance(tree,int):
            return (tree,),None,None
        left,right=map(prepare,tree)
        return left[0]+right[0],left,right

    top=prepare(balanced(0,len(ordinary)) if layout is None else layout)
    if sorted(top[0]) != list(range(len(ordinary))):
        raise ValueError("decomposition leaves must list every column exactly once")
    peak_width = peak_states = 0

    def visit(node,outside):
        nonlocal peak_width, peak_states
        ids,left_node,right_node=node
        port = intersection(canonical(ordinary[i] for i in ids),outside)
        if left_node is None:
            table = {f:{0:0} for f in range(1<<len(port))}
            if ids and port:
                index=ids[0]
                assert len(port)==1 and port[0]==ordinary[index]
                table[0][port[0]] = 1<<index
        else:
            left_cols=tuple(ordinary[i] for i in left_node[0])
            right_cols=tuple(ordinary[i] for i in right_node[0])
            left_port,left = visit(left_node,canonical(outside+right_cols))
            right_port,right = visit(right_node,canonical(outside+left_cols))
            merged=canonical(left_port+right_port)
            lmap=restrictions(merged,left_port)
            rmap=restrictions(merged,right_port)
            pmap=restrictions(merged,port)
            inside={image(port,mask) for mask in range(1<<len(port))}
            table={}
            for f in range(1<<len(merged)):
                lhs=left[project_value(f,lmap)]
                rhs=right[project_value(f,rmap)]
                target=table.setdefault(project_value(f,pmap),{})
                for u,mask_left in lhs.items():
                    for v,mask_right in rhs.items():
                        if u^v in inside:
                            target.setdefault(u^v,mask_left|mask_right)
        peak_width=max(peak_width,len(port))
        peak_states=max(peak_states,sum(map(len,table.values())))
        return port,table

    port,states=visit(top,canonical(roots))
    return port,states,peak_width,peak_states


def spectrum(base, primal, dual, t, layout=None):
    ordinary,roots=augment(base,primal,dual,t)
    port,states,width,peak=state_table(ordinary,roots,layout)
    found={}
    for b in range(1<<t):
        root_values=b<<t
        ext=functional(roots,root_values)
        if ext is None:
            continue
        block=states[project_value(ext,port)]
        for a in range(1<<t):
            target=image(roots,a)
            if target not in block or a^b in found:
                continue
            c=block[target]
            chosen=tuple(v for i,v in enumerate(ordinary) if c>>i & 1)
            alpha=functional(roots+chosen,root_values)
            assert alpha is not None
            d=sum(((v & alpha).bit_count()%2)<<i for i,v in enumerate(ordinary))
            assert not c&d and not image(base,c)
            assert image(primal,c)==a and image(dual,d)==b
            found[a^b]=(c,d)
    return found,width,peak
