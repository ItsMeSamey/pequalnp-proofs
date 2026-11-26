from random import Random


def sums(cols):
    out=[0]
    for c in cols:
        out += [v^c for v in out]
    return out


def trace(cols, ambient_rank, boundary_rank):
    result=set()
    for dual in range(1<<ambient_rank):
        good=[c for c in cols if not (c&dual).bit_count()%2]
        pvals={0}
        for c in good:
            pvals.update([v^c for v in pvals])
        for p in pvals:
            if p<1<<boundary_rank:
                result.add((p,dual% (1<<boundary_rank)))
    return result


def terminal_circuit(cols):
    values=sums(cols)
    minimal=[]
    for mask,val in enumerate(values):
        if mask and not val and not any(mask&m==m for m in minimal):
            if mask&7==7:
                return True
            minimal.append(mask)
    return False


if __name__=='__main__':
    rng=Random(22973)
    checked=0
    for _ in range(650):
        # Bits 0,1 form W; bits 2,3,4 are private to X and 5,6 are private to Y.
        x=[rng.randrange(1,32) for _ in range(6)]
        if len(set(sums(x[:3])))!=8:
            continue
        y=[rng.randrange(4)^(rng.randrange(4)<<5) for _ in range(5)]
        target=trace(y,7,2)
        for code in range(8):
            rep=[j+1 for j in range(3) if code>>j&1]
            if trace(rep,2,2)==target:
                break
        else:
            raise AssertionError("no boundary-only surrogate")
        assert terminal_circuit(x+y)==terminal_circuit(x+rep)
        checked+=1
    print(checked,"exact trace replacements preserved the three-terminal circuit predicate")
