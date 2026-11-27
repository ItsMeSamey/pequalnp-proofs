"""Literal graph and its minimal positive and maximal negative inputs."""
E=(6,24,17,33,66,132,264,528,160,640,576,320,288)
V=1023
F=[any(m&e==e for e in E) for m in range(1024)]
Z=[m for m in range(1024) if not F[m] and all(F[m|(1<<i)] for i in range(10) if not m>>i&1)]
