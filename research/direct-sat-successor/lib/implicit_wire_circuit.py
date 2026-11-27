"""Cumulative original-circuit compiler using implicit products."""
from boolean_value_automata import BudgetExceeded,dot,indices,minimize
from implicit_wire_product import implicit_product


def solve(n, gates, output, *, order=None, budget=1000000, rank_cap=256):
    order = tuple(range(n)) if order is None else tuple(order)
    if sorted(order) != list(range(n)) or budget < 0:
        raise ValueError('invalid raw order or budget')
    if output < 0 or output.bit_length() > n+len(gates)+1:
        raise ValueError('invalid output mask')
    for j,(a,b) in enumerate(gates):
        if min(a,b)<0 or max(a,b).bit_length()>n+j+1:
            raise ValueError('invalid operand mask')
    cost = {'budget':budget,'charged_cells':0,'operations':0,'max_pre_width':0,'max_min_width':0}

    def reserve(d):
        # Dense scalar slots for both matrices per layer plus cut vectors;
        # polynomial elimination/bit-arithmetic overhead is outside this metric.
        cells = 1+sum(d)+2*sum(a*b for a,b in zip(d,d[1:]))
        if cost['charged_cells']+cells>budget:
            cost['declined_cells']=cells
            raise BudgetExceeded
        cost['charged_cells']+=cells
        cost['operations']+=1
        cost['max_pre_width']=max(cost['max_pre_width'],max(d))

    def compact(p):
        result, w = minimize(p)
        cost['max_min_width']=max(cost['max_min_width'],max(result[0]))
        return result,w

    def atom(index):
        d = [1]*(n+1)
        reserve(d)
        matrix=[((1,),(1,)) for _ in range(n)]
        if index is not None:
            matrix[index]=((0,),(1,))
        return d,1,matrix,1

    def combine(p,q,product):
        a,s,psteps,t=p
        b,u,qsteps,v=q
        if product:
            remaining=budget-cost['charged_cells']
            result=implicit_product(p,q,rank_cap=rank_cap,cell_budget=remaining)
            info=result['cost']
            cost['last_product']=dict(info, prior_cells=cost['charged_cells'])
            cost['candidates']=cost.get('candidates',0)+info['candidates']
            if result['status']=='skip':
                cost['decline_reason']=result['reason']
                raise BudgetExceeded
            # Conservative charge for compact dense slots, including cut vectors.
            amount=1+(n+1)*info['max_reached_rank']+info['compact_cells']
            if amount>remaining:
                cost['declined_cells']=amount
                raise BudgetExceeded
            cost['charged_cells']+=amount
            cost['operations']+=1
            cost['max_pre_width']=max(cost['max_pre_width'],info['max_reached_rank'])
            cost['max_min_width']=max(cost['max_min_width'],max(result['program'][0]))
            return result['program']
        d=[x+y for x,y in zip(a,b)]
        reserve(d)
        steps=[]
        for i,(pm,qm) in enumerate(zip(psteps,qsteps)):
            layer=[]
            for m1,m2 in zip(pm,qm):
                rows=tuple(m1)+tuple(y<<a[i+1] for y in m2)
                layer.append(rows)
            steps.append(tuple(layer))
        return compact((d,s | u<<a[0],steps,t | v<<a[-1]))[0]

    try:
        constant=atom(None)
        zero=([0]*(n+1),0,[((),())]*n,0)
        wires=[constant]+[None]*n
        for pos,raw in enumerate(order):
            wires[raw+1]=atom(pos)
        def affine(mask):
            selected=[wires[i] for i in indices(mask)]
            if not selected:
                return zero
            acc=selected[0]
            for item in selected[1:]:
                acc=combine(acc,item,False)
            return acc
        for a,b in gates:
            wires.append(combine(affine(a),affine(b),True))
        out=affine(output)
        reserve(out[0])
        _,word=compact(out)
        if word is None:
            return {'status':'unsat','cost':cost}
        witness=sum(((word>>i)&1)<<v for i,v in enumerate(order))
        actual=1|(witness<<1)
        for j,(a,b) in enumerate(gates):
            actual |= (dot(actual,a)&dot(actual,b))<<(n+j+1)
        if not dot(actual,output):
            raise AssertionError('original witness failed replay')
        return {'status':'sat','witness':witness,'cost':cost}
    except BudgetExceeded:
        return {'status':'skip','cost':cost}
