"""Standalone bounded large-order product oracle. Run only in allocated native slot."""
import fcntl
import hashlib
import json
import math
import os
import resource
import signal
from fractions import Fraction
from pathlib import Path

lock_path = "/workspace/scratch/pnp-native-search.lock"
lock = open(lock_path, "a")
def inode(stat):
    return stat.st_dev, stat.st_ino
assert inode(os.fstat(lock.fileno())) == inode(os.stat(lock_path))
fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
assert inode(os.fstat(lock.fileno())) == inode(os.stat(lock_path))
resource.setrlimit(resource.RLIMIT_CPU, (4, 4))
signal.alarm(9)
def memory_guard(*_):
    assert resource.getrusage(resource.RUSAGE_SELF).ru_maxrss < 64 * 1024
signal.signal(signal.SIGPROF, memory_guard)
signal.setitimer(signal.ITIMER_PROF, .025, .025)

import extreme_cnf_digit as target
def sha(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()
assert sha(target.__file__) == "decc3e8416bdc29e18ca5292b4efc7f6c8a6539e1e799694e7d8d7a6afadebf0"

def fixture(kind, size):
    clauses = [(i + 1,) for i in range(size)]
    positions = list(range(2 * size))
    if kind == "free":
        positions = [p ^ 1 for p in positions]
    else:
        clauses[0] = (-1,)
        if kind == "det":
            clauses[1] = (-2,)
    return clauses, positions

def local_reference(kind, size):
    clauses, packet = fixture(kind, size)
    length = len(packet)
    t = length - 1
    den = math.prod(-q for q in range(-length, length) if q)
    # Direct product-rule differentiation of the defining integer polynomial.
    coeff = {}
    for d in range(1-length, length):
        c, j = 1, 0
        for q in range(-length, length):
            if q != d:
                c, j = c*(t-q), j*(t-q) + c*2*length
        coeff[d] = c, j
    rows = [packet.index(2*i) for i in range(size)]
    dormant = [clauses[i][0] > 0 and row != 0 for i, row in enumerate(rows)]
    # For each X, each designated factor starts at order >=1. At the sum of
    # these orders no higher derivative can contribute. Unary COPY sums to 1.
    total = 0
    for word in range(1 << size):
        product = 1
        for i, row in enumerate(rows):
            order = int(dormant[i])
            val = sum(coeff[j-row][order] for j, p in enumerate(packet)
                      if (word >> (p//2)) & 1)
            if clauses[i][0] < 0:
                val = den-val
            product *= val
        total += product
    return sum(dormant), Fraction(total, den**size)

cases = []
size, copies = 8, 8
tie_order, tie_coeff = local_reference("tie",size)
for special in ["det","free"]:
    special_order, special_coeff = local_reference(special,size)
    clauses, packets = [], []
    for k in range(copies):
        cs, pk = fixture("tie" if k+1 < copies else special,size)
        offset = k*size
        clauses.extend([((1 if x>0 else -1)*(abs(x)+offset),) for (x,) in cs])
        packets.append([p+2*offset for p in pk])
    order = tie_order*(copies-1)+special_order
    coefficient = tie_coeff**(copies-1)*special_coeff
    assert coefficient and coefficient.denominator % 2
    valuation = (abs(coefficient.numerator) & -abs(coefficient.numerator)).bit_length()-1
    answer = target.from_clauses(size*copies,clauses,packets,
                                 center=2*size-1,word_cap=1<<copies)
    assert answer["status"]=="exact" and answer["bit"]==1
    assert answer["order"]==order and answer["first_bit_position"]==valuation
    assert answer["outside_bits"]==copies*(size-1)
    assert (answer["outside_bits"]>order if special=="det" else answer["outside_bits"]<order)
    cases.append(dict(case=special,order=order,expected_valuation=valuation,
                      residue_mod_32=(coefficient.numerator//(1<<valuation))*
                      pow(coefficient.denominator,-1,32)%32,
                      outside=answer["outside_bits"],bits=size*copies,
                      baseline_words=answer["word_bound"],reported_bit=answer["bit"]))
memory_guard()
print(json.dumps(dict(harness=sha(__file__), target=sha(target.__file__),cases=cases,
                      rss_kib=resource.getrusage(resource.RUSAGE_SELF).ru_maxrss)))
