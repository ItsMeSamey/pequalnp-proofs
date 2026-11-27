"""Verified marker-block domains with original physical-byte replay."""
from collections import defaultdict
from collections.abc import Mapping
from event_csp import EventCSP, Record, ScheduleMismatch
from padding_cnf import encode
from stack_alias import _slots, decode_alias


def build(challenge,n,aliases,table,initial,bottom,outputs,*,schedule=None):
    """Schedule gives first-byte operations by marker index; all tails must stay."""
    challenge=tuple(tuple(c) for c in challenge)
    slots=tuple(_slots(aliases,n))
    zero=encode(challenge,n,0).splitlines(keepends=True)
    one=encode(challenge,n,(1<<(n+1))-1).splitlines(keepends=True)
    count=len(slots)
    if zero[:-count]!=one[:-count]:
        raise ValueError("nonconstant canonical prefix")
    prefix=b"".join(zero[:-count])
    blocks=tuple(zip(zero[-count:],one[-count:]))
    if schedule is not None:
        if isinstance(schedule,Mapping):
            if any(type(i) is not int or not 0<=i<count for i in schedule):
                raise ValueError("invalid macro schedule index")
            schedule=tuple(schedule.get(i,"stay") for i in range(count))
        else:
            schedule=tuple(schedule)
        if len(schedule)!=count or any(op not in ("stay","push","pop") for op in schedule):
            raise ValueError("invalid marker schedule")
    table={key:tuple(action) for key,action in table.items()}
    outputs=dict(outputs)
    if initial not in outputs or any(type(b) not in (int,bool) or b not in (0,1) for b in outputs.values()):
        raise ValueError("invalid output table")
    symbols={bottom}
    for (q,top,byte),action in table.items():
        if q not in outputs or type(byte) is not int or not 0<=byte<256 or len(action)<2 or action[0] not in outputs:
            raise ValueError("invalid byte transition")
        symbols.add(top)
        if action[1]=="push" and len(action)==3 and action[2]!=bottom:
            symbols.add(action[2])
        elif len(action)!=2 or not(action[1]=="stay" or action[1]=="pop" and top!=bottom):
            raise ValueError("invalid stack operation")
    alphabet=set(prefix)
    for pair in blocks:
        for word in pair:
            if not word:
                raise ValueError("empty marker spelling")
            alphabet.update(word)
    if any((q,t,b) not in table for q in outputs for t in symbols for b in alphabet):
        raise ValueError("incomplete table on physical alphabet")

    def advance(q,memory,byte):
        action=table[q,memory[-1],byte]
        if action[1]=="push":
            memory.append(action[2])
        elif action[1]=="pop":
            if len(memory)==1:
                raise ValueError("physical underflow")
            memory.pop()
        return action[0]

    q,memory=initial,[bottom]
    for byte in prefix:
        q=advance(q,memory,byte)
    frontier={(q,memory[-1])}
    frames=[(None,(top,)) for top in memory[:-1]]
    metrics=dict(prefix_bytes=len(prefix),spelling_bytes=sum(len(w) for p in blocks for w in p),
                 validated_table_entries=len(table),completeness_checks=len(outputs)*len(symbols)*len(alphabet),
                 first_lookups=0,tail_lookups=0,record_candidates=0)
    domains,operations={},[]
    kinds=defaultdict(list)
    previous={}
    for i,(words,(name,offset)) in enumerate(zip(blocks,slots)):
        first=[(state,top,bit,table[state,top,w[0]]) for state,top in frontier for bit,w in enumerate(words)]
        metrics["first_lookups"]+=len(first)
        ops={action[1] for _,_,_,action in first}
        if len(ops)!=1 or schedule is not None and schedule[i] not in ops:
            raise ScheduleMismatch(f"uncertified first operation at marker {i}")
        op=ops.pop()
        operations.append(op)
        restored=()
        if op=="push":
            frames.append((i,tuple({top for _,top,_,_ in first})))
        elif op=="pop":
            if not frames:
                raise ScheduleMismatch(f"pop below bottom at marker {i}")
            push,restored=frames.pop()
            if push is not None:
                kinds[push,i].append(("restore",0))
        records=set()
        fail=object()
        for bit,word in enumerate(words):
            by_top=defaultdict(list)
            for state,top,choice,action in first:
                if choice!=bit:
                    continue
                tops=restored if op=="pop" else (action[2],) if op=="push" else (top,)
                for newtop in tops:
                    by_top[newtop].append((state,top,action[0]))
                    metrics["record_candidates"]+=1
            for newtop,entries in by_top.items():
                # The suffix can see the newly restored top immediately after a pop.
                after={state:state for state in outputs}
                for byte in reversed(word[1:]):
                    before={}
                    for state in outputs:
                        action=table[state,newtop,byte]
                        before[state]=after[action[0]] if action[1]=="stay" else fail
                    after=before
                    metrics["tail_lookups"]+=len(outputs)
                for state,top,entry in entries:
                    exit_state=after[entry]
                    if exit_state is fail:
                        raise ScheduleMismatch(f"non-stay marker tail at marker {i}, bit {bit}")
                    records.add(Record((state,top),(exit_state,newtop),bit,word))
        domains[i]=tuple(records)
        frontier={r.after for r in records}
        if i:
            kinds[i-1,i].append(("path",0))
        if name in previous:
            j,old_offset=previous[name]
            kinds[j,i].append(("alias",old_offset^offset))
        previous[name]=(i,offset)
    domains[count]=(0,1)
    kinds[count-1,count].append(("output",0))

    def allowed(x,y,relations):
        for kind,param in relations:
            if kind=="output" and outputs[x.after[0]]!=y:
                return False
            if kind=="path" and x.after!=y.before:
                return False
            if kind=="restore" and x.before[1]!=y.after[1]:
                return False
            if kind=="alias" and x.bit^y.bit!=param:
                return False
        return True

    pairs=tuple(sorted(kinds))
    constraints=tuple((i,j,frozenset((x,y) for x in domains[i] for y in domains[j]
                                     if allowed(x,y,kinds[i,j]))) for i,j in pairs)

    def replay(witness):
        if any(i not in witness or witness[i] not in domain for i,domain in domains.items()):
            raise ValueError("invalid macro assignment")
        if any((witness[i],witness[j]) not in relation for i,j,relation in constraints):
            raise ValueError("incompatible macro records")
        key=sum(witness[i].bit<<i for i in range(count))
        raw=prefix+b"".join(witness[i].byte for i in range(count))
        actual_n,actual_challenge,actual_key,underlying=decode_alias(raw,slots)
        if (actual_n,tuple(actual_challenge),actual_key)!=(n,challenge,key):
            raise ValueError("original formula or signed key mismatch")
        state,stack=initial,[bottom]
        for byte in prefix:
            state=advance(state,stack,byte)
        for i in range(count):
            row=witness[i]
            if (state,stack[-1])!=row.before:
                raise ValueError("macro entry disagrees with byte run")
            for byte in row.byte:
                state=advance(state,stack,byte)
            if (state,stack[-1])!=row.after:
                raise ValueError("macro exit disagrees with byte run")
        if outputs[state]!=witness[count]:
            raise ValueError("original terminal output mismatch")
        return dict(physical=raw,key=key,underlying=underlying,prediction=int(outputs[state]))

    result=EventCSP(domains,constraints,pairs,tuple(range(count)),count,tuple(operations),replay)
    result.metrics=metrics
    return result
