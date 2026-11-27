"""Compare independently generated circuit witnesses with the reusable checker."""
from collections import Counter
import json
import fork_certificate as engine
from tiny_fork_soundness import require, run, wires


def rejects(thunk, substring):
    try:
        thunk()
    except ValueError as error:
        require(substring in str(error),f'unexpected rejection: {error}')
    else:
        raise ValueError('invalid fixture accepted: '+substring)


def main():
    checks=Counter()
    def observe(care,n,gates,groups,outside):
        model={'literals':['positive']*n,'fixed_cost':0}
        table,bits,u,live,_=engine.prepare(care,n,model)
        require(u==outside and live==n,'engine coordinate classification')
        evidence=engine.orientation_witnesses(table,bits,u)
        general,positive=engine.derive_edges(table,bits,u,evidence)
        real=[]
        for fork,group in sorted(groups.items()):
            signed=len(set(group.values()))>1
            mask=sum(1<<i for i in group)
            require(all(mask&e!=e for e in general),'engine rejected signed group')
            if not signed:
                require(all(mask&e!=e for e in positive),'engine rejected positive group')
            real.append((mask,signed))
        require(engine.ordered_filter(table,u)(tuple(real)),'engine rejected real group order')
        checks['actual groupings accepted']+=1
        if groups:
            gates_n=len(gates)
            plan=[{'positive':0,'signed':len(bits),'ordered':True,'partitions':0}]
            cert=engine.make_certificate(care,n,model,gates_n,plan)
            rejects(lambda:engine.verify_case(care,n,model,cert),'compatible branch ordering')
            checks['false lower bounds rejected']+=1
    result=run(observe)
    model={'literals':['positive']*2,'fixed_cost':0}
    xor={0:0,1:1,2:1,3:0}
    good=engine.make_certificate(xor,2,model,1,[])
    require(engine.verify_case(xor,2,model,good)['total_lower_bound']==2,'baseline XOR bound')
    rejects(lambda:engine.prepare([(0,0),(0,1)],2,model),'duplicate care pattern')
    rejects(lambda:engine.prepare([(0,None)],2,model),'invalid care label')
    rejects(lambda:engine.prepare([],2,model),'empty care')
    rejects(lambda:engine.verify_case({0:0,1:1,3:0},2,model,good),'mismatch')
    bad=dict(good,budget=4)
    rejects(lambda:engine.verify_case(xor,2,model,bad),'uncovered topology')
    general,positive=engine.derive_edges(xor,[0,1],0,{'general':{},'monotone':{}})
    require(3 in general and 3 in positive,'XOR corner must exclude pair')
    mixed={0:0,1:1,2:0,3:0}
    general,positive=engine.derive_edges(mixed,[0,1],0,{'general':{},'monotone':{}})
    require(3 not in general and 3 in positive,'mixed corner classification')
    # First coordinate supplies both physical phases. The DAG uses both;
    # the second coordinate supplies only its negative phase. It computes XOR.
    physical=(('!',2),('&',0,2),('&',1,3),('|',4,5))
    mixed_model={'literals':['both_live','negative'],'fixed_cost':1}
    projected={}
    for x in range(4):
        a=x&1
        b=x>>1
        packed=a | ((1-a)<<1) | ((1-b)<<2)
        projected[x]=wires(3,physical,packed)[-1]
    require(projected==xor,'mixed-literal DAG truth')
    table,bits,u,live,_=engine.prepare(projected,2,mixed_model)
    require(table=={x^2:y for x,y in xor.items()} and bits==[1] and u==1 and live==3,
            'mixed-literal source accounting')
    plan=[{'positive':1,'signed':1,'ordered':True,'partitions':0}]
    attempted=engine.make_certificate(projected,2,mixed_model,5,plan)
    rejects(lambda:engine.verify_case(projected,2,mixed_model,attempted),'compatible branch ordering')
    checks['mixed-literal false bound rejected']=1
    print(json.dumps(dict(circuits=result,engine=dict(checks),invalid_cert_or_input_fixtures=5),sort_keys=True))

if __name__=='__main__':
    main()
