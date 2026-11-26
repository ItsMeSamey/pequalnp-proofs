# A two-wire cut for threshold two

Let C(n) denote minimum binary monotone circuit size for threshold two on n inputs. Suppose a subset of k inputs, 2≤k<n, reaches the output exclusively through two wires computed from those inputs alone. The other n−k inputs can enter the decoder without restriction. Write E and D for the encoder and decoder sizes; disconnected dead gates can be discarded. Then

    E + D ≥ C(k) + C(n−k+2) − 1.

Indeed, the two-bit encoding distinguishes weight classes 0, 1 and ≥2 by testing the other inputs at zero or a singleton. By monotonicity along a chain through the three classes, their respective codes are 00, one or both of {01,10}, and 11. If both singleton orientations occur, the decoder already computes threshold two on n−k+2 independent bits, and adding one AND to the encoder realizes threshold two on k inputs. If one orientation occurs, the encoder supplies threshold two and OR-all. Removing the first OR-all site by symbolic-top propagation yields a threshold-two circuit with at most E−1 gates. Conversely, attaching a sorter (one OR, one AND) on two independent primary bits to the decoder gives threshold two on n−k+2 inputs with D+2 gates. These inequalities give the same bound.

When equality holds, in the first case the appended AND gives a minimum k-input circuit and the decoder is minimum on n−k+2 inputs. In the second case symbolic-top propagation removes just one gate, necessarily the OR realizing the first OR-all signal. A first realization cannot be an AND because both operands would already have been OR-all. The augmented decoder is minimum. Accordingly the original AND count in either case equals the sum of the AND counts of two threshold optima at the indicated arities minus one.

At n=10, k=4,…,8 the size bound gives at least 25. For k=3 or 9 it gives 24, with AND count at equality exactly 2+4−1=5 by the known composition of the three- and nine-input optima. Hence a minimum ten-input, seven-AND candidate admits no such autonomous block on three or more inputs.

At n=13, k=3,…,12 the bounds in order are 32,33,33,33,34,34,33,33,33,32 using C(3),…,C(12)=4,7,10,13,16,19,21,24,27,29. This excludes such an autonomous block in every 31-gate candidate, at every AND count. To apply this lemma to an incidence graph, the two output wires must form a cut in the circuit itself.
