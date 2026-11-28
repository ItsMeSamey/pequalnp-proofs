"""Exact signed integer contraction via odd-prime images and scalar D.1 calls."""
from dataclasses import dataclass
from math import isqrt
from typing import Callable, Sequence


@dataclass(frozen=True)
class Vertex:
    shore: int
    ports: tuple[int, ...]
    # Exactly one oracle is supplied. A residue oracle receives (port bits, odd prime).
    boolean: Callable | None = None
    residue: Callable | None = None
    abs_bound: int = 1


@dataclass(frozen=True)
class Limits:
    max_calls: int
    max_precision: int
    max_prime: int
    max_output_bits: int


class LimitExceeded(RuntimeError):
    """No result is certified within the specified resource cap."""


def odd_primes(limit):
    for n in range(3, limit + 1, 2):
        if all(n % d for d in range(3, isqrt(n) + 1, 2)):
            yield n


def contract(wires: int, vertices: Sequence[Vertex], backend, limits: Limits):
    """Return (signed integer, completed scalar calls).

    backend(wires, vertices, precision, entry) returns the canonical scalar residue
    modulo 2**precision, ell=1, using entry(vertex_index, ordered_port_bits).
    It must evaluate the identical graph with THESE integer entry representatives.
    Each exceptional abs_bound is a trusted uniform bound on its ORIGINAL entries.
    The caller separately checks D.1 scale, port degrees, description/entry cost
    and backend workspace. Caps bound this adapter, not work inside an opaque oracle.
    """
    if wires < 0 or min(vars(limits).values()) < 0:
        raise ValueError("negative size or cap")
    port_count = [{}, {}]
    exceptional = []
    for i, v in enumerate(vertices):
        if v.shore not in (0, 1) or (v.boolean is None) == (v.residue is None):
            raise ValueError("invalid shore or entry interface")
        if v.abs_bound < 0:
            raise ValueError("negative magnitude bound")
        for edge in v.ports:
            if not 0 <= edge < wires or edge in port_count[v.shore]:
                raise ValueError("invalid or repeated edge on one shore")
            port_count[v.shore][edge] = i
        if v.residue is not None:
            exceptional.append(v)
    if any(len(side) != wires for side in port_count):
        raise ValueError("missing incident edge")
    if any(v.abs_bound == 0 for v in exceptional):
        return 0, 0
    if wires + 1 > limits.max_output_bits:
        raise LimitExceeded("original absolute bound exceeds output-bit cap")
    extent = 1 << wires
    for v in exceptional:
        if extent.bit_length() + v.abs_bound.bit_length() - 1 > limits.max_output_bits:
            raise LimitExceeded("original absolute bound exceeds output-bit cap")
        extent *= v.abs_bound
        if extent.bit_length() > limits.max_output_bits:
            raise LimitExceeded("original absolute bound exceeds output-bit cap")

    def run(prime, precision):
        def entry(index, bits):
            v = vertices[index]
            if len(bits) != len(v.ports) or any(bit not in (0, 1) for bit in bits):
                raise ValueError("malformed backend entry request")
            if v.boolean is not None:
                value = v.boolean(bits)
                if value not in (0, 1):
                    raise ValueError("Boolean oracle returned a non-Boolean entry")
                return int(value)
            return v.residue(bits, prime) % prime
        value = backend(wires, vertices, precision, entry)
        if not isinstance(value, int) or value < 0 or value.bit_length() > precision:
            raise ValueError("backend must return the canonical scalar residue")
        return value

    if not exceptional:
        if limits.max_calls < 1 or wires + 1 > limits.max_precision:
            raise LimitExceeded("Boolean scalar call exceeds cap")
        value = run(None, wires + 1)
        if value > extent:
            raise ValueError("backend result exceeds Boolean path bound")
        return value, 1

    answer, modulus, calls = 0, 1, 0
    for prime in odd_primes(limits.max_prime):
        if calls >= limits.max_calls:
            raise LimitExceeded("scalar-call cap reached")
        if wires + 1 > limits.max_precision:
            raise LimitExceeded("odd-prime lift exceeds precision cap")
        lift_bound = 1 << wires
        for _ in exceptional:
            if lift_bound.bit_length() + (prime-1).bit_length() - 1 > limits.max_precision:
                raise LimitExceeded("odd-prime lift exceeds precision cap")
            lift_bound *= prime - 1
            if lift_bound.bit_length() > limits.max_precision:
                raise LimitExceeded("odd-prime lift exceeds precision cap")
        lifted = run(prime, lift_bound.bit_length())
        calls += 1
        if lifted > lift_bound:
            raise ValueError("backend result exceeds nonnegative lift bound")
        delta = ((lifted - answer) * pow(modulus, -1, prime)) % prime
        answer += delta * modulus
        modulus *= prime
        if modulus > 2 * extent:
            signed = answer if 2 * answer < modulus else answer - modulus
            if abs(signed) > extent:
                raise ValueError("CRT output exceeds certified original extent")
            return signed, calls
    raise LimitExceeded("prime cap exhausted before signed reconstruction")
