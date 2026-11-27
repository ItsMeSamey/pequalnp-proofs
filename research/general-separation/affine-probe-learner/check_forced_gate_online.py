"""Tiny explicit full-secret majority oracle for forced gates."""
from dataclasses import dataclass


@dataclass(frozen=True)
class Wire:
    index: int
    offset: int = 0

    def read(self, seed):
        if self.index < 0:
            return self.offset
        return ((seed >> self.index) & 1) ^ self.offset


@dataclass(frozen=True)
class Probe:
    wire: Wire
    left: Wire = Wire(-1)
    right: Wire = Wire(-1)

    def read(self, seed):
        return self.wire.read(seed) ^ (self.left.read(seed) & self.right.read(seed))


class ExactLocal:
    def __init__(self, width, candidates=None):
        self.width = width
        self.candidates = tuple(range(1 << width)) if candidates is None else candidates
        self.transcript = ()

    def copy(self):
        other = ExactLocal(self.width, self.candidates)
        other.transcript = self.transcript
        return other

    def predict(self, probe):
        return int(2*sum(probe.read(s) for s in self.candidates) > len(self.candidates))

    def feedback(self, probe, label):
        guess = self.predict(probe)
        survivors = tuple(s for s in self.candidates if probe.read(s) == label)
        assert survivors
        if guess != label:
            assert 2*len(survivors) <= len(self.candidates)
        self.candidates = survivors
        self.transcript += ((probe, label, guess),)
        assert sum(y != g for _,y,g in self.transcript) <= self.width


def completions(local, n):
    result = {}
    for seed in local.candidates:
        result.setdefault(seed % (1 << n), []).append(seed)
    return result


def force(local, index, left, right):
    # Expose only the native wire with zero offset. The returned wire decodes
    # its stored truth value as the intended product for either chosen label.
    probe = Probe(Wire(index), left, right)
    label = 1 ^ local.predict(probe)
    local.feedback(probe, label)
    return Wire(index, label)


def explicit_output(program, x):
    gates, output = program
    def raw(spec):
        kind, index, offset = spec
        if kind == 'x':
            return ((x >> index) & 1) ^ offset
        if kind == 'c':
            return offset
        return values[index] ^ offset
    values = []
    for left, right in gates:
        values.append(1 ^ (raw(left) & raw(right)))
    return raw(output)


class AlwaysOne(ExactLocal):
    def predict(self, probe):
        return 1

    def feedback(self, probe, label):
        self.candidates = tuple(s for s in self.candidates if probe.read(s) == label)
        assert self.candidates
        self.transcript += ((probe, label, 1),)


def run(n, cap, programs, secret, fake=False):
    width = n+(n+1)*cap
    factory = AlwaysOne if fake else ExactLocal
    committed = ()
    used = errors = 0
    original = set(range(1 << n))
    for program in programs:
        gates, output = program
        assert len(gates) <= cap
        trial = factory(width)
        for probe, label, old_guess in committed:
            assert trial.predict(probe) == old_guess != label
            trial.feedback(probe, label)
        before = completions(trial,n)
        assert set(before) == original and secret in original
        next_wire = n+used
        wires = []

        def decode(spec):
            kind, index, offset = spec
            if kind == 'g':
                base = wires[index]
                return Wire(base.index,base.offset ^ offset)
            return Wire(index if kind == 'x' else -1,offset)

        for j,(left,right) in enumerate(gates):
            product = force(trial,next_wire,decode(left),decode(right))
            wires.append(Wire(product.index,product.offset ^ 1))
            next_wire += 1
            groups = completions(trial,n)
            assert set(groups) == original
            for x, extensions in groups.items():
                assert len(before[x]) == len(extensions)*(1 << (j+1))
                expected = explicit_output((gates[:j+1],('g',j,0)),x)
                assert all(wires[-1].read(s) == expected for s in extensions)
        probe = Probe(decode(output))
        for s in trial.candidates:
            assert probe.read(s) == explicit_output(program,s % (1 << n))
        guess = trial.predict(probe)
        answer = explicit_output(program,secret)
        if guess == answer:
            continue
        trial.feedback(probe,answer)
        committed = trial.transcript
        used += len(gates)
        errors += 1
        original = {x for x in original if explicit_output(program,x) == answer}
        assert set(completions(trial,n)) == original
        if errors == n+1:
            assert fake
            for i in range(n+used,width):
                literal = Probe(Wire(i))
                trial.feedback(literal,1 ^ trial.predict(literal))
            assert len(trial.transcript) == width+1
            assert all(label != guess for _,label,guess in trial.transcript)
            assert set(completions(trial,n)) == original
            assert all(len(xs) == 1 for xs in completions(trial,n).values())
            return errors
    assert errors <= n
    return errors


if __name__ == '__main__':
    for n in (1,2,3):
        for cap in (0,1,2):
            left = ('x',0,1)
            right = ('x',n-1,0)
            gates = [(left,right),(('g',0,1),('g',0,0))][:cap]
            constant_zero = ('c',0,0)
            output = ('g',cap-1,0) if gates else left
            literals = [([],('x',i,0)) for i in range(n)]
            programs = [(gates,constant_zero),(gates,output)] + literals*2
            for x in range(1 << n):
                run(n,cap,programs,x)
            # Always-one deliberately violates the premise. Even synthetic
            # gate labels now have offset zero. Keep unused reserve for padding.
            forced = [(gates,constant_zero)] + [([],constant_zero)]*n
            assert run(n,cap,forced,0,fake=True) == n+1
    print('Gate completions, rollback, replay and terminal padding agree.')
