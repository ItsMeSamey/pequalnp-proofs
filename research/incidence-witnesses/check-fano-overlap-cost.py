"""Minimize two physical fork bounds at each number of common accepted flags."""
import runpy
from pathlib import Path

import numpy as np

lower = runpy.run_path(str(Path(__file__).with_name("check-fano-or-splits.py")))["lower"]
masks = np.arange(65536)
weight = np.array([m.bit_count() for m in range(65536)])
cost = np.array([lower(m) for m in range(65536)])
best = [999] * 15
for b_size in range(1, 16):
    extension = np.where(weight == b_size, cost, 999)
    for bit in range(16):
        halves = extension.reshape(-1, 2, 1 << bit)
        np.minimum(halves[:, 0], halves[:, 1], out=halves[:, 0])
    score = 1 + cost + extension[65535 ^ masks]
    for a_size in range(max(1, 16-b_size), 16):
        overlap = a_size + b_size - 16
        best[overlap] = min(best[overlap], int(score[weight == a_size].min()))
print(best)
