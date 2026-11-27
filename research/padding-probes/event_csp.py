"""Compile canonical physical DIMACS words and a visible byte table to a binary CSP."""
from collections import defaultdict
from collections.abc import Mapping
from dataclasses import dataclass
from padding_cnf import encode
from stack_alias import _slots, decode_alias


class ScheduleMismatch(ValueError):
    """Operation uniformity not certified by the forward state overapproximation."""


@dataclass(frozen=True)
class Record:
    before: tuple
    after: tuple
    bit: object
    byte: object


@dataclass
class EventCSP:
    domains: dict
    constraints: tuple
    edges: tuple
    slot_events: tuple
    output: int
    operations: tuple
    _replay: object

    def replay(self, witness):
        return self._replay(witness)


def build(challenge,n,aliases,table,initial,bottom,outputs,*,schedule=None):
    """Return byte event domains, conjoined pair relations, and a terminal bit.

    schedule may be inferred, be a per-byte sequence, or be an index map with
    default stay. Pins can restrict Record.bit at a marker's slot_events index.
    """
    challenge=tuple(tuple(c) for c in challenge)
    slots=tuple(_slots(aliases,n))
    zero=encode(list(challenge),n,0).splitlines(keepends=True)
    one=encode(list(challenge),n,(1<<(n+1))-1).splitlines(keepends=True)
    prefix=len(zero)-len(slots)
    events=[(-1,(b,)) for line in zero[:prefix] for b in line]
    starts=[]
    for i,(a,b) in enumerate(zip(zero[prefix:],one[prefix:])):
        starts.append(len(events))
        events.extend((i,(a[j] if j<len(a) else None,b[j] if j<len(b) else None))
                      for j in range(max(len(a),len(b))))
    L=len(events)
    if schedule is not None:
        if isinstance(schedule,Mapping):
            if any(type(i) is not int or not 0<=i<L for i in schedule):
                raise ValueError("schedule position out of range")
            schedule=tuple(schedule.get(i,"stay") for i in range(L))
        else:
            schedule=tuple(schedule)
        if len(schedule)!=L or any(op not in ("stay","push","pop") for op in schedule):
            raise ValueError("invalid byte schedule")
    table={key:tuple(action) for key,action in table.items()}
    outputs=dict(outputs)
    if initial not in outputs or any(type(b) not in (int,bool) or b not in (0,1) for b in outputs.values()):
        raise ValueError("invalid output table")
    symbols={bottom}
    for (q,top,b),action in table.items():
        if q not in outputs or type(b) is not int or not 0<=b<256 or len(action)<2 or action[0] not in outputs:
            raise ValueError("invalid transition")
        symbols.add(top)
        if action[1]=="push" and len(action)==3 and action[2]!=bottom:
            symbols.add(action[2])
        elif len(action)!=2 or not(action[1]=="stay" or action[1]=="pop" and top!=bottom):
            raise ValueError("invalid stack operation")
    alphabet={b for _,opts in events for b in opts if b is not None}
    if any((q,t,b) not in table for q in outputs for t in symbols for b in alphabet):
        raise ValueError("incomplete transition table on physical alphabet")
    domains={}
    kinds=defaultdict(list)
    stack=[]
    operations=[]
    frontier={(initial,bottom,None)}
    last_slot=-1
    for p,(slot,options) in enumerate(events):
        transitions=[]
        ops=set()
        for state,top,old_bit in frontier:
            choices=(None,) if slot<0 else ((0,1) if slot!=last_slot else (old_bit,))
            for bit in choices:
                byte=options[0 if bit is None else bit]
                action=(state,"stay") if byte is None else table[state,top,byte]
                ops.add(action[1])
                transitions.append((state,top,bit,byte,action))
        if len(ops)!=1 or schedule is not None and schedule[p] not in ops:
            raise ScheduleMismatch(f"uncertified operation at byte {p}")
        op=ops.pop()
        operations.append(op)
        restored=()
        if op=="pop":
            if not stack:
                raise ScheduleMismatch(f"pop below bottom at byte {p}")
            push,restored=stack.pop()
            kinds[push,p].append(("restore",0))
        elif op=="push":
            stack.append((p,tuple({top for _,top,_,_,_ in transitions})))
        records=set()
        for state,top,bit,byte,action in transitions:
            next_tops=restored if op=="pop" else ((action[2],) if op=="push" else (top,))
            for new_top in next_tops:
                records.add(Record((state,top),(action[0],new_top),bit,byte))
        domains[p]=tuple(records)
        frontier={(r.after[0],r.after[1],r.bit) for r in records}
        if p:
            kinds[p-1,p].append(("path",int(slot>=0 and slot==last_slot)))
        last_slot=slot
    previous={}
    for p,(variable,offset) in zip(starts,slots):
        if variable in previous:
            old,old_offset=previous[variable]
            kinds[old,p].append(("alias",old_offset^offset))
        previous[variable]=(p,offset)
    domains[L]=(0,1)
    kinds[L-1,L].append(("output",0))

    def allowed(x,y,conditions):
        for kind,param in conditions:
            if kind=="output":
                if outputs[x.after[0]]!=y:
                    return False
            elif kind=="path":
                if x.after!=y.before or param and x.bit!=y.bit:
                    return False
            elif kind=="alias":
                if x.bit^y.bit!=param:
                    return False
            elif x.before[1]!=y.after[1]:
                return False
        return True
    pairs=tuple(sorted(kinds))
    constraints=tuple((i,j,frozenset((x,y) for x in domains[i] for y in domains[j]
                                    if allowed(x,y,kinds[i,j]))) for i,j in pairs)

    def replay(witness):
        if any(i not in witness or witness[i] not in domain for i,domain in domains.items()):
            raise ValueError("missing or invalid event assignment")
        if any((witness[i],witness[j]) not in relation for i,j,relation in constraints):
            raise ValueError("invalid event pair")
        raw=bytes(witness[i].byte for i in range(L) if witness[i].byte is not None)
        actual_n,actual_challenge,key,underlying=decode_alias(raw,slots)
        if (actual_n!=n or tuple(actual_challenge)!=challenge or
                key!=sum(witness[p].bit<<i for i,p in enumerate(starts))):
            raise ValueError("physical spelling or key mismatch")
        state=initial
        memory=[bottom]
        for b in raw:
            action=table[state,memory[-1],b]
            state=action[0]
            if action[1]=="push":
                memory.append(action[2])
            elif action[1]=="pop":
                if len(memory)==1:
                    raise ValueError("underflow on physical replay")
                memory.pop()
        if outputs[state]!=witness[L]:
            raise ValueError("original table disagrees with output")
        return dict(physical=raw,key=key,underlying=underlying,prediction=int(outputs[state]))

    return EventCSP(domains,constraints,pairs,tuple(starts),L,tuple(operations),replay)
