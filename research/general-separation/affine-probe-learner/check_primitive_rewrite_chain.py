"""Independent structural verifier for primitive_rewrite_chain certificates."""
from dataclasses import replace


class Invalid(ValueError):
    pass


def require(condition):
    if not condition:
        raise Invalid("invalid rewrite certificate")


class Terms:
    def __init__(self):
        self.by_key = {}
        self.keys = []

    def term(self, *key):
        if key not in self.by_key:
            self.by_key[key] = len(self.keys)
            self.keys.append(key)
        return self.by_key[key]


def integer(x):
    return type(x) is int


def load(nodes, n, pool):
    ids = []
    open_term = []
    for node in nodes:
        require(type(node) is tuple and len(node) > 0)
        op, *args = node
        if op in ('const','var'):
            require(len(args) == 1 and integer(args[0]))
            require(0 <= args[0] < (2 if op == 'const' else n))
            result = pool.term(*node)
            opened = False
        elif op == 'hole':
            require(not args)
            result = pool.term(op)
            opened = True
        else:
            require(op in ('and','or','nand','not'))
            require(len(args) == (1 if op == 'not' else 2))
            require(all(integer(a) and 0 <= a < len(ids) for a in args))
            result = pool.term(op,*(ids[a] for a in args))
            opened = any(open_term[a] for a in args)
        ids.append(result)
        open_term.append(opened)
    return ids,open_term


def plug(nodes, ids, opened, context, replacement, pool):
    # Transform a single shared hole globally. References off its support keep
    # their canonical IDs, even when they are identical to the left redex.
    cache = {}
    stack = [(context,False)]
    while stack:
        i,ready = stack.pop()
        if i in cache:
            continue
        op,*args = nodes[i]
        if not opened[i]:
            cache[i] = ids[i]
        elif op == 'hole':
            cache[i] = replacement
        elif ready:
            cache[i] = pool.term(op,*(cache[a] for a in args))
        else:
            stack.append((i,True))
            stack.extend((a,False) for a in args if a not in cache)
    return cache[context]


def endpoints(n,gates,output,j,pool):
    require(integer(n) and n >= 0 and integer(j) and 0 <= j < 1 << n)
    z,o = pool.term('const',0),pool.term('const',1)
    var = [pool.term('var',i) for i in range(n)]
    refs = {-1:z,-2:o,**dict(enumerate(var))}
    bits = {-1:0,-2:1,**{i:(j >> (n-1-i)) & 1 for i in range(n)}}
    for i,(u,v) in enumerate(gates,n):
        require(integer(u) and integer(v) and u in refs and v in refs)
        refs[i] = pool.term('nand',refs[u],refs[v])
        bits[i] = 1 ^ (bits[u] & bits[v])
    require(integer(output) and output in refs and not bits[output])
    source = refs[output]

    def threshold(k):
        if k == -1:
            return z
        if k == (1 << n)-1:
            return source
        prefix = z
        start = 0
        for power in reversed(range(n)):
            if ((k+1) >> power) & 1:
                cube = o
                for i in range(n-power):
                    literal = var[i] if (start >> (n-1-i)) & 1 else pool.term('not',var[i])
                    cube = pool.term('and',cube,literal)
                prefix = pool.term('or',prefix,cube)
                start += 1 << power
        return pool.term('and',source,prefix)
    return threshold(j),threshold(j-1)


def match(pattern,root,pool,env):
    if isinstance(pattern,str):
        if pattern in env:
            return env[pattern] == root
        env[pattern] = root
        return True
    key = pool.keys[root]
    if pattern[0] in ('const','hole'):
        return key == pattern
    return (key[0] == pattern[0] and len(key) == len(pattern) and
            all(match(p,r,pool,env) for p,r in zip(pattern[1:],key[1:])))


def checked_step(nodes,ids,opened,pool,previous,following,step):
    indices = (previous,following,step.left,step.right,step.context)
    require(all(integer(i) and 0 <= i < len(ids) for i in indices))
    require(opened[step.context] and not any(opened[i] for i in indices[:4]))
    require(step.rule in RULES)
    lhs,rhs = RULES[step.rule]
    for a,b in ((step.left,step.right),(step.right,step.left)):
        env = {}
        if match(lhs,ids[a],pool,env) and match(rhs,ids[b],pool,env):
            break
    else:
        raise Invalid("pattern mismatch")
    require(plug(nodes,ids,opened,step.context,ids[step.left],pool) == ids[previous])
    require(plug(nodes,ids,opened,step.context,ids[step.right],pool) == ids[following])


def verify_step(nodes,previous,following,step,n):
    pool = Terms()
    ids,opened = load(nodes,n,pool)
    checked_step(nodes,ids,opened,pool,previous,following,step)
    return True


def verify(n,gates,output,j,chain):
    pool = Terms()
    first,last = endpoints(n,gates,output,j,pool)
    ids,opened = load(chain.nodes,n,pool)
    require(len(chain.roots) == len(chain.steps)+1)
    for root in chain.roots:
        require(integer(root) and 0 <= root < len(ids) and not opened[root])
    require((ids[chain.roots[0]],ids[chain.roots[-1]]) == (first,last))
    for a,b,step in zip(chain.roots,chain.roots[1:],chain.steps):
        checked_step(chain.nodes,ids,opened,pool,a,b,step)
    return True


def conjunction(a,b):
    return ('and',a,b)


def disjunction(a,b):
    return ('or',a,b)


def nand(a,b):
    return ('nand',a,b)


A,B,C = 'A','B','C'
zero,one = ('const',0),('const',1)
p,q = conjunction,disjunction
RULES = {
    'and_one': (p(A,one),A),
    'and_zero': (p(A,zero),zero),
    'zero_and': (p(zero,A),zero),
    'or_zero': (q(A,zero),A),
    'zero_or': (q(zero,A),A),
    'or_assoc': (q(q(A,B),C),q(A,q(B,C))),
    'sibling': (q(p(A,('not',B)),p(A,B)),A),
    'distribute': (p(A,q(B,C)),q(p(A,B),p(A,C))),
    'and_commute': (p(A,B),p(B,A)),
    'shield': (p(A,nand(B,C)),p(A,nand(p(A,B),p(A,C)))),
    'and_swap_tail': (p(p(A,B),C),p(p(A,C),B)),
    'and_assoc': (p(p(A,B),C),p(A,p(B,C))),
    'and_idem': (p(A,A),A),
    'neg_and': (p(('not',A),A),zero),
    'nand_00': (p(A,nand(zero,zero)),A),
    'nand_0m': (p(A,nand(zero,A)),A),
    'nand_m0': (p(A,nand(A,zero)),A),
    'nand_mm': (p(A,nand(A,A)),zero),
}


def reject(f,*args):
    try:
        f(*args)
    except Invalid:
        return
    raise AssertionError("malformed certificate accepted")


def controls():
    from primitive_rewrite_chain import build_chain
    examples = [(0,(),-1,0),(1,(),0,0),(2,(),1,2),
                (3,((0,1),(3,3),(3,2),(4,5),(6,6)),7,7)]
    # Generate actual chains for negative points only, without relying on the
    # producer's source evaluator.
    examples.extend((3,((0,1),(3,3),(3,2),(4,5),(6,6)),7,j) for j in range(8))
    shared = False
    for n,gates,out,j in examples:
        try:
            endpoints(n,gates,out,j,Terms())
        except Invalid:
            continue
        chain = build_chain(n,gates,out,j)
        assert verify(n,gates,out,j,chain)
        if not chain.steps:
            continue
        step = chain.steps[0]
        reject(verify,n,gates,out,j,replace(chain,roots=chain.roots[:-1]))
        for bad in (replace(step,rule='no_such_rule'),replace(step,context=step.left),
                    replace(step,right=step.context),replace(step,left=-1)):
            reject(verify_step,chain.nodes,*chain.roots[:2],bad,n)
        reject(verify,n,gates,out,j,replace(chain,nodes=chain.nodes+(('not',len(chain.nodes)),)))
        if shared:
            continue
        # Manufactured multi-use context with an identical, untargeted
        # copy of the redex. A partial plug is semantically correct but is
        # neither of this certificate's two ordered results.
        nodes = (('var',0),('const',1),('and',0,1),('hole',),
                 ('or',3,3),('and',4,2),('or',2,2),('and',6,2),
                 ('or',0,0),('and',8,2),('or',0,2),('and',10,2),
                 ('and',0,0))
        good = replace(step,context=5,left=2,right=0,rule='and_one')
        assert verify_step(nodes,7,9,good,1)
        reject(verify_step,nodes,7,11,good,1)
        reject(verify_step,nodes,7,9,replace(good,rule='and_idem'),1)
        # Wrong expression with the same truth table and valid topological form.
        reject(verify_step,nodes,7,9,replace(good,right=12),1)
        shared = True
    assert shared


if __name__ == '__main__':
    controls()
    print('Structural chain and adversarial certificate checks passed.')
