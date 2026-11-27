"""Reduce source 3-CNF to the fixed paired physical byte machine and validate witnesses."""
from collections import deque
from collections.abc import Mapping
from dataclasses import dataclass
from importlib import import_module
from padding_cnf import encode
from stack_alias import decode_alias


def fixed_dfa():
    """A complete byte table independent of the source size and content."""
    start=("skip",9)
    sink=("reject",)
    def advance(q,b):
        if q==sink:
            return sink
        if q[0]=="skip":
            if b!=10:
                return q
            return ("marker",True,(),True) if q[1]==1 else ("skip",q[1]-1)
        _,eq,buf,first=q
        if not first:
            return ("marker",eq,buf,b==10)
        if b==10:
            return sink
        buf=buf+(int(b==45),)
        if len(buf)==3:
            if not (len(set(buf))==1 if eq else any(buf)):
                return sink
            eq,buf=not eq,()
        return ("marker",eq,buf,False)
    ids={start:0}
    queue=deque([start])
    table={}
    outputs={}
    while queue:
        q=queue.popleft()
        i=ids[q]
        outputs[i]=int(q==("marker",True,(1,),True))
        for b in range(256):
            r=advance(q,b)
            if r not in ids:
                ids[r]=len(ids)
                queue.append(r)
            table[i,0,b]=(ids[r],"stay")
    return table,0,0,outputs


def _satisfies(clauses,mask):
    return all(any(bool(mask>>(abs(l)-1)&1)==(l>0) for l in c) for c in clauses)


@dataclass
class Compiled:
    n: int
    clauses: tuple
    slots_n: int
    aliases: tuple
    occurrences: dict
    anchors: dict
    assignments: dict
    dummy_bits: dict
    exact_twice: bool

    def lift(self,raw):
        n,challenge,key,values=decode_alias(raw,self.aliases)
        if n!=self.slots_n or challenge or not values[self.aliases[-1]]:
            raise ValueError("wrong carrier or enable")
        for pos in range(0,self.slots_n,6):
            group=(key>>pos)&63
            if (group&7) not in (0,7) or group>>3==0:
                raise ValueError("physical equality or OR test failed")
        mask=sum(values[a]<<(v-1) for v,a in self.anchors.items() if v<=self.n)
        if any(values[name]!=values[self.anchors[v]] for v,ids in self.occurrences.items()
               for name in ids) or not _satisfies(self.clauses,mask):
            raise ValueError("physical word fails source projection")
        return mask

    def word(self,mask):
        if type(mask) is not int or mask<0 or mask.bit_length()>self.n or not _satisfies(self.clauses,mask):
            raise ValueError("expected satisfying original assignment")
        underlying={name:(mask>>(v-1))&1 for name,v in self.assignments.items()}
        underlying.update(self.dummy_bits)
        underlying[self.aliases[-1]]=1
        key=sum((underlying[abs(a)]^int(a<0))<<i for i,a in enumerate(self.aliases))
        return encode([],self.slots_n,key)


def compile_source(n,clauses,*,exact_twice=False):
    if type(n) is not int or n<0 or type(exact_twice) is not bool:
        raise ValueError("invalid source dimension or mode")
    clauses=tuple(tuple(c) for c in clauses)
    prepared=[]
    for c in clauses:
        if len(c)>3 or any(type(l) is not int or not 1<=abs(l)<=n for l in c):
            raise ValueError("expected valid signed clauses of width at most three")
        if not c:
            prepared.extend(((n+1,)*3,(-n-1,)*3))
        else:
            prepared.append(c+(c[-1],)*(3-len(c)))
    next_id=0
    def fresh():
        nonlocal next_id
        next_id+=1
        return next_id
    occurrences={}
    assignments={}
    ors=[]
    for c in prepared:
        row=[]
        for literal in c:
            j=fresh()
            v=abs(literal)
            occurrences.setdefault(v,[]).append(j)
            assignments[j]=v
            row.append(j if literal>0 else -j)
        ors.append(tuple(row))
    eq=[]
    for v,ids in occurrences.items():
        links=[fresh() for _ in range(len(ids)+int(not exact_twice))]
        assignments.update(dict.fromkeys(links,v))
        for i,j in enumerate(ids):
            eq.append((links[i],j,links[(i+1)%len(links)]))
    dummy={}
    for i in range(2*len(prepared)):
        if exact_twice:
            d=fresh()
            if i%2==0:
                f=fresh()
                dummy[f]=0
            dummy[d]=0
            ors.append((d,-d,f))
        else:
            group=tuple(fresh() for _ in range(3))
            dummy.update(dict.fromkeys(group,1))
            ors.append(group)
    aliases=tuple(l for e,o in zip(eq,ors) for group in (e,o) for l in group)+(fresh(),)
    return Compiled(n,clauses,len(aliases)-1,aliases,
                    {v:tuple(js) for v,js in occurrences.items()},
                    {v:js[0] for v,js in occurrences.items()},assignments,dummy,exact_twice)


_MODULES={"gaussian":"event_gaussian_solver","compressed":"event_compressed_solver",
          "flat":"event_flat_solver","rank2":"event_rank2_solver","ie":"event_ie_solver",
          "period":"event_period_solver","block":"event_block_solver"}
_DEFAULTS={"gaussian":{"exception_cap":0,"branch_cap":128},
           "compressed":{"omission_cap":8,"state_cap":128,"work_cap":1024},
           "flat":{"omission_cap":8,"dimension_cap":8},
           "rank2":{"omission_cap":8,"codimension_cap":8},
           "ie":{"omission_cap":8,"branch_cap":512},
           "period":{"choice_cap":256},"block":{"state_cap":2048,"step_cap":8192}}


def solve(n,clauses,*,exact_twice=False,source_pins=(),stages=None,fallback_limit=0):
    """Return a source SAT mask, a complete UNSAT verdict, or bounded UNKNOWN."""
    job=compile_source(n,clauses,exact_twice=exact_twice)
    if fallback_limit is not None and (type(fallback_limit) is not int or fallback_limit<0):
        raise ValueError("invalid fallback assignment limit")
    fixed={}
    conflict=False
    for v,b in (source_pins.items() if isinstance(source_pins,Mapping) else source_pins):
        if type(v) is not int or not 1<=v<=n or type(b) is not int or b not in (0,1):
            raise ValueError("invalid original pin")
        conflict |= fixed.setdefault(v,b)!=b
    attempts=[]
    def result(status,witness=None,physical=None,**extra):
        return dict(status=status,witness=witness,physical=physical,attempts=attempts,**extra)
    if conflict:
        return result("UNSAT",reason="contradictory source pins")
    table,initial,bottom,outputs=fixed_dfa()
    def verified(raw):
        state=initial
        for byte in raw:
            state=table[state,bottom,byte][0]
        if outputs[state]!=1:
            raise ArithmeticError("original physical predictor rejected alleged SAT word")
        mask=job.lift(raw)
        for v,b in fixed.items():
            if v not in job.anchors and b:
                mask|=1<<(v-1)
        if (not _satisfies(job.clauses,mask) or
            any((mask>>(v-1)&1)!=b for v,b in fixed.items())):
            raise ArithmeticError("original CNF or pin mismatch")
        return result("SAT",mask,raw)
    pins=tuple((job.anchors[v],b) for v,b in fixed.items() if v in job.anchors)
    if stages is None:
        stages=("gaussian","compressed","flat","rank2","block")
    for item in stages:
        name,options=(item,{}) if isinstance(item,str) else item
        if name not in _MODULES:
            raise ValueError("unknown source stage")
        options=dict(options)
        allowed=set(_DEFAULTS[name])|{"backend","codebooks"}
        if name=="flat":
            allowed.add("max_flat_rank")
        if name=="block":
            allowed.discard("codebooks")
        if set(options)-allowed:
            raise ValueError("unsupported physical stage option")
        options={**_DEFAULTS[name],**options}
        physical=import_module(_MODULES[name]).solve([],job.slots_n,job.aliases,table,initial,
                     bottom,outputs,id_pins=pins,schedule={},**options)
        status=physical["status"]
        attempts.append(dict(stage=name,status=status,metrics=physical["metrics"],
                             reason=physical.get("reason")))
        for sample in physical["samples"]:
            if sample["prediction"]==1:
                return verified(sample["physical"])
        if status=="constant" and physical.get("value")==0:
            return result("UNSAT",reason="complete physical negative")
        if status!="unknown":
            raise ArithmeticError("physical stage lost its guaranteed zero anchor or positive witness")
    active=[v for v in job.anchors if v<=n and v not in fixed]
    base=sum(b<<(v-1) for v,b in fixed.items())
    total=1<<len(active)
    limit=total if fallback_limit is None else min(total,fallback_limit)
    for i in range(limit):
        mask=base|sum(((i>>j)&1)<<(v-1) for j,v in enumerate(active))
        if _satisfies(job.clauses,mask):
            attempts.append(dict(stage="source-enumeration",examined=i+1,total=total))
            return verified(job.word(mask))
    attempts.append(dict(stage="source-enumeration",examined=limit,total=total))
    return result("UNSAT" if limit==total else "UNKNOWN",
                  reason="source search complete" if limit==total else "source assignment cap")
