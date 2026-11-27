"""Check exhaustive optional-tap cases against realizable tiny circuits."""
from itertools import product
import fork_certificate as engine


def check(ok, message):
    if not ok:
        raise ValueError(message)


def refuses(action):
    try:
        action()
    except ValueError:
        return
    raise ValueError('accepted invalid family claim')


def receipts(care, model, budget):
    choices=[('positive','negative','both_live') if lit=='optional' else (lit,) for lit in model['literals']]
    parts=[]
    for lits in product(*choices):
        exclusive=dict(literals=list(lits),fixed_cost=model['fixed_cost'])
        cert=engine.make_certificate(care,len(lits),exclusive,budget,[])
        parts.append(dict(literals=list(lits),certificate=cert))
    return parts


def exercise(care,model,budget):
    verify=lambda branches:engine.verify_optional_family(care,len(model['literals']),model,branches)
    parts=receipts(care,model,budget)
    verify(parts)
    for i in range(len(parts)):
        refuses(lambda:verify(parts[:i]+parts[i+1:]))
    refuses(lambda:verify(parts+[parts[-1]]))
    mixed=receipts(care,model,budget-1)[:1]+parts[1:]
    refuses(lambda:verify(mixed))
    return verify,parts


def main():
    mux={x:(x>>1&1 if x&1 else x>>2&1) for x in range(8)}
    model=dict(literals=['optional','positive','positive'],fixed_cost=1)
    verify,_=exercise(mux,model,3)
    over=receipts(mux,model,4)
    # The one-sided cases have valid four-total-gate exclusions. The actual
    # both-live MUX uses precisely three binary gates and one fixed gate.
    plan=[dict(positive=0,signed=0,ordered=True,partitions=0)]
    for branch in over[:2]:
        exclusive=dict(literals=branch['literals'],fixed_cost=1)
        cert=engine.make_certificate(mux,3,exclusive,4,plan)
        engine.verify_case(mux,3,exclusive,cert)
        branch['certificate']=cert
    refuses(lambda:verify(over[:2]))
    refuses(lambda:verify(over))
    # The one-gate OR of data inputs uses neither selector tap. Making a
    # second axis optional forces a full nine-branch Cartesian product.
    dummy={x:int(bool(x&2 or x&4)) for x in range(8)}
    model=dict(literals=['optional','optional','positive'],fixed_cost=2)
    check(all(dummy[x]==dummy[x^1] for x in dummy),'selector is not dummy')
    verify,parts=exercise(dummy,model,2)
    check(len(parts)==9,'incorrect Cartesian size')
    refuses(lambda:verify(receipts(dummy,model,3)))
    # A constant uses neither literal of the only optional axis.
    constant={0:0,1:0}
    model=dict(literals=['optional'],fixed_cost=0)
    refuses(lambda:engine.verify_optional_family(constant,1,model,receipts(constant,model,0)))
    print('optional family passed: MUX, absent selector, dummy constant, nine-branch product')


if __name__=='__main__':
    main()
