"""Certified grouped-system counter using the shared quadratic_image Gaussian sum."""
import sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1] / 'direct-sat-algebra'))
from quadratic_image import gauss
from quadratic_target import affine_domain


class Unsupported(ValueError):
    """The accepted fragment could not be certified."""


def parse(system):
    if system.n < 0 or any(symbol <= 1 for symbol, _ in system.definitions):
        raise ValueError("invalid input dimension or definition symbol")
    rank_bits = set()
    equations = []

    for symbol, products in [*system.definitions, (1, system.final)]:
        if symbol != 1:
            if symbol.bit_count() != 1 or symbol < (2 << system.n) or symbol in rank_bits:
                raise ValueError('invalid definition')
        allowed = ((2 << system.n) - 1) | sum(rank_bits)
        anf = {symbol >> 1}  # Monomial bitmask; 0 represents the constant.
        for term in products:
            if any(f < 0 or f & ~allowed for f in term):
                raise ValueError('unavailable operand')
            factors = set(term) - {1}
            if 0 in factors or any(f ^ 1 in factors for f in factors):
                continue
            if len(factors) > 2:
                raise Unsupported('product has more than two distinct nonconstant factors')
            monomials = {0}
            for f in factors:
                items = ([0] if f & 1 else []) + [1 << j for j in range(f.bit_length()-1) if f & (2 << j)]
                result = set()
                for m in monomials:
                    for bit in items:
                        result.symmetric_difference_update([m | bit])
                monomials = result
            anf ^= monomials
        equations.append(anf)
        if symbol != 1:
            rank_bits.add(symbol)
    N = max([system.n] + [b.bit_length()-1 for b in rank_bits])
    if len(rank_bits) != N-system.n:
        raise ValueError('noncontiguous auxiliary coordinates')
    return N,equations


