# Exact majority after planted disjoint quadratic mistakes

Fix the uniform evaluator that reads a sparse quadratic over the binary field and evaluates it on a single hidden seed. The learner considered here takes the exact majority over seeds consistent with its mistaken probes, breaking ties toward zero. After a prefix of mistakes on disjoint triples, deciding its next majority is PP-complete, even if the new quadratic has an interaction graph consisting of vertex-disjoint paths of length at most four. Each histogram bin is #P-complete under polynomial-time metric reductions. Every prefix of the planted disjoint-triple sequence retains the full affine hull.

## The planted prefix

Allocate M ordered triples (x_j,y_j,z_j). The seed sets every triple to (0,0,1). Present x_j y_j+z_j in order. The true bit is one. Even conditional on all prior labels the fresh z_j balances the two histogram bins, so every probe is a mistake. A committed triple has z_j=1+x_j y_j, with four equiprobable assignments, indexed by its two ports x_j,y_j. The points (0,0,1),(0,1,1),(1,0,1),(1,1,0) affinely span the full triple. Varying one factor at a time proves the same for each product of constrained triples and unconstrained fresh triples. This seed is independent of the circuit below.

## Encoding circuit evaluation in one more probe

Take a NAND circuit C with n explicitly supplied input bits, one output gate, g gates, and public constants. First append a designated output identity so the new output is a sink. Then normalize fanout, counting repeated input pins separately. A binary distribution tree of identity copies supplies the uses of any gate or input with fanout greater than two. Each copy is two NAND gates with second input one. The number of gates and wires after normalization is linear in the original number of gates, wires and input pins.

Use the first g planted triples as gate ports. Their z coordinates are already the NAND of their ports. Store the n external input bits w and 2g independent multiplier bits in the x,y coordinates of ceil((n+2g)/2) additional planted triples. Ignore the z coordinates of these triples. Let p be the number of leftover port bits, either zero or one. Thus M=g+ceil((n+2g)/2), h=3M, and the committed feasible set has 2^(2M) seeds.

For each gate input pin i, let L_i be its port bit plus the wire source, which is an input bit, an earlier gate's z coordinate, or a constant. Take the new quadratic

    Q = z_out + sum_i lambda_i L_i.

Over each fixed input and assignment of the gate ports, summing (-1)^Q over all multipliers gives zero if any wiring equation fails. Otherwise it gives 2^(2g) times (-1)^z_out. The circuit is acyclic, so each external input has exactly one consistent assignment of the 2g port bits. Summing the p unused bits gives the exact signed histogram difference

    W = N_0 - N_1 = 2^(2g+p) (2^n - 2 #C).

Here #C counts accepting input words. Knowing either bin determines W because N_0+N_1=2^(2M). Each bin lies in #P by guessing all free port coordinates and evaluating the probe. An arbitrary polynomial-time witness verifier compiles in polynomial time to a circuit with one input per witness bit and unchanged accepting count, giving #P-hardness under one metric reduction. A polynomial-time probabilistic machine with a prescribed polynomial random-bit budget likewise compiles to a circuit preserving its acceptance probability. Choosing majority one exactly when W<0 therefore gives PP-hardness. Conversely, sampling the free port coordinates uniformly gives the appropriate PP machine. The same hardness holds with ties excluded as shown below. [Strict-majority satisfiability and counting conventions](https://par.nsf.gov/servlets/purl/10392779)

The interaction graph has an edge for every nonzero quadratic monomial on distinct coordinates. Each pin contributes a private port leaf joined to its private multiplier, which is also joined to the source when the source is a coordinate. Sources, leaves and multipliers occupy disjoint sets of coordinates. Each source has at most two uses. Thus a component is an isolated vertex, an isolated edge, or a source with one or two arms of length two. Public constants add no interaction edge to the source. There are at most 4g quadratic monomials. The evaluator reads O((g+n+1) log(h+2)) bits for the sparse stream including indices, headers and the prefix. Conversely a dense coefficient format costs polynomial size as well. No gate, wire, copy or multiplier requires a succinct circuit representation.

## Strict thresholds and a final planted mistake

Given a circuit or CNF F on n variables with A accepting words, and 0≤K<2^n, use a new circuit on two selector bits and n word bits. Two selector values evaluate F. On the other two values, read the remaining selector bit and word together as an (n+1)-bit integer and accept the first D=2^(n+1)−2K−1 such integers. The comparator has O(n+1) gates before normalization, and the evaluation branches can share one copy of F. This circuit accepts exactly 2A+D words, whose excess over half of all words is 2(A−K)−1. Its sign decides A>K and can never be zero. This handles strict thresholds including A=K. For K=2^n the answer is always no. Taking the usual majority threshold gives the claimed tie-free PP-hardness.

For exact counts one may instead replace F by C(w,b,c)=F(w) AND b AND c. Its accepting count is A, at most one quarter of the input space. Hence the final majority is strictly zero. At the original public seed all multipliers vanish and z_out=1, so this final probe is also a genuine mistake. The formula for W still recovers A. This establishes exact-count hardness even for the fully mistaken stream, while the strict-threshold reduction establishes hardness of the majority decision before observing its true label.

The result concerns this prediction rule. Uniformly sampling the survivor set after the prefix is easy, and there are only M+1 probes in the constructed stream on 3M secret bits. No lower bound for all learners with a given mistake budget follows from the counting reduction.
