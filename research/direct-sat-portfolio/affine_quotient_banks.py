"""Synthesize explicit bounded affine-input truth tables for the quotient route.

Each bank is (tuple_of_port_masks, truth_table_integer). Table bit j is the
output on little-endian address j. References use the portfolio convention;
bank j supplies signal n+1+j before compilation.
"""
from affine_quotient import _bits


def synthesize_banks(n, banks, output, *, table_entry_limit):
    if type(n) is not int or n < 0 or type(table_entry_limit) is not int or table_entry_limit < 0:
        raise ValueError("invalid synthesis dimensions or limit")
    gates = []
    signals = []
    entries = 0
    raw_mask = (1 << (n+1))-1

    def substitute(word):
        if type(word) is not int or word < 0 or word.bit_length() > n+1+len(signals):
            raise ValueError("invalid or forward bank reference")
        answer = word & raw_mask
        for index in _bits(word >> (n+1)):
            answer ^= signals[index]
        return answer

    for ports, table in banks:
        ports = tuple(substitute(word) for word in ports)
        arity = len(ports)
        if arity >= (table_entry_limit-entries).bit_length():
            raise ValueError("table entry limit exceeded")
        size = 1 << arity
        if type(table) is not int or table < 0 or table.bit_length() > size:
            raise ValueError("invalid truth table")
        entries += size
        # Little-endian packed conversion keeps extraction linear in table size.
        packed = table.to_bytes((size+7)//8, "little")
        anf = bytearray((packed[i//8] >> (i%8)) & 1 for i in range(size))
        for coordinate in range(arity):
            bit = 1 << coordinate
            for mask in range(size):
                if mask & bit:
                    anf[mask] ^= anf[mask ^ bit]
        needed = bytearray(anf)
        for mask in range(size-1, 0, -1):
            if needed[mask] and mask.bit_count() > 1:
                needed[mask & (mask-1)] = 1
        monomials = [0] * size
        monomials[0] = 1
        result = anf[0]
        for mask in range(1, size):
            if not needed[mask]:
                continue
            bit = mask & -mask
            operand = ports[bit.bit_length()-1]
            if mask == bit:
                monomials[mask] = operand
            else:
                gates.append((monomials[mask ^ bit], operand))
                monomials[mask] = 1 << (n+len(gates))
            if anf[mask]:
                result ^= monomials[mask]
        signals.append(result)
    return tuple(gates), substitute(output), dict(banks=len(signals),
                                                   table_entries=entries,
                                                   synthesized_ands=len(gates))
