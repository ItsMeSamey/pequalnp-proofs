"""Project the fixed paired predictor's accepting runs after EQ and dummy propagation."""
from importlib import import_module


def aliases(job):
    return tuple((job.anchors[job.assignments[abs(a)]] if abs(a) in job.assignments else abs(a))
                 * (1 if a>0 else -1) for a in job.aliases)


def solve_positive(job,fixed,name,options):
    """One row per nondummy OR using the true three marker signs as its codeword."""
    modules={"projected_gaussian":"event_affine_factors","projected_compressed":"event_compressed_ie",
             "projected_rank2":"event_rank2_fourier"}
    output=("enable",)
    domains={output:(1,)}
    for v in job.occurrences:
        domains["v",v]=(fixed[v],) if v in fixed else (0,1)
    pairs=[]
    for pos in range(0,job.slots_n,6):
        triple=job.aliases[pos+3:pos+6]
        if all(abs(a) in job.dummy_bits for a in triple):
            if not any(job.dummy_bits[abs(a)]^int(a<0) for a in triple):
                raise ArithmeticError("normalized dummy is false")
            continue
        row=("or",pos//6)
        fields=[(job.assignments[abs(a)],int(a<0)) for a in triple]
        allowed=[]
        for word in range(1,8):
            assigned={}
            for j,(v,offset) in enumerate(fields):
                bit=(word>>j&1)^offset
                if assigned.setdefault(v,bit)!=bit or bit not in domains["v",v]:
                    break
            else:
                allowed.append(word)
        domains[row]=tuple(allowed)
        for j,(v,offset) in enumerate(fields):
            pairs.append((row,("v",v),tuple((word,(word>>j&1)^offset) for word in allowed)))
    books={var:{value:value for value in domain} for var,domain in domains.items()}
    decision=import_module(modules[name]).solve(domains,pairs,output,codebooks=books,**options)
    witness=decision["witnesses"].get(1)
    if witness is not None:
        source=sum(witness["v",v]<<(v-1) for v in job.occurrences if v<=job.n)
        source|=sum(b<<(v-1) for v,b in fixed.items())
        return "SAT",source,decision
    if decision["status"]=="empty":
        return "UNSAT",None,decision
    if decision["status"]!="unknown":
        raise ArithmeticError("invalid positive-only backend status")
    return "UNKNOWN",None,decision
