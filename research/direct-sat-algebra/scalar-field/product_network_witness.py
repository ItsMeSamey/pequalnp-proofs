"""Recover a raw witness for a product network and one raw bit."""
from affine_binomial import power
from product_network_inequality import compile_instance
from product_network_basepoint import solve

def add_term(poly, ex, c):
    value=poly.get(ex,0)^c
    if value:
        poly[ex]=value
    else:
        poly.pop(ex,None)

def choose_parameters(field,orders,poly):
    """A nonzero character sum on independent cyclic groups."""
    parameters=[]
    for order in orders:
        tried=set()
        reduced=None
        # Shoup bounds the first primitive-containing prefix in this order.
        for candidate in range(1,field.size):
            step=power(field,candidate,(field.size-1)//order)
            u=1
            for _ in range(min(len(poly),order)):
                if u not in tried:
                    tried.add(u)
                    restricted={}
                    for ex,c in poly.items():
                        add_term(restricted,ex[1:],field.mul(c,power(field,u,ex[0])))
                    if restricted:
                        reduced=restricted
                        break
                u=field.mul(u,step)
            if reduced is not None:
                break
        if reduced is None:
            raise ArithmeticError('lost a nonzero character sum')
        parameters.append(u)
        poly=reduced
    return parameters

def witness(chart,target,form,required=1):
    f=chart.field
    instance=compile_instance(f,chart.frames,chart.shift,chart.edges,
                              chart.output_offset,target,form,required)
    if instance is None:
        return None
    edges=[(i,j,t,b) for (i,j,t,_),b in zip(chart.edges,chart.edge_targets(target))]
    forced=frozenset(k for i,j,t,b in edges if b for k in (i,j))
    supports={forced.union(i for i,e in enumerate(ex) if e)
              for c,ex in instance.polynomial if c}
    for support in sorted(supports,key=lambda s:(len(s),tuple(sorted(s)))):
        base=solve(f,len(chart.frames),edges,support)
        if base is None:
            continue
        poly={}
        for c,ex in instance.polynomial:
            if any(e and i not in support for i,e in enumerate(ex)):
                continue
            for a,e in zip(base.values,ex):
                c=f.mul(c,power(f,a,e))
            label=tuple(sum(ex[v]*s for v,s in zip(comp.vertices,comp.exponents))
                        %comp.order for comp in base.components)
            add_term(poly,label,c)
        if not poly:
            continue
        parameters=choose_parameters(f,[comp.order for comp in base.components],poly)
        values=list(base.values)
        for u,comp in zip(parameters,base.components):
            for v,s in zip(comp.vertices,comp.exponents):
                values[v]=f.mul(values[v],power(f,u,s%comp.order))
        raw=chart.raw_input(values)
        from quadratic_image import evaluate
        if chart.output(values)!=target or evaluate((form,),raw)!=required:
            raise ArithmeticError('lifted witness failed target or original bit')
        return raw
    return None
