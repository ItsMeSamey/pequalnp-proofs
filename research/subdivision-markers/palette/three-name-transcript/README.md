# End-to-end binary three-name certificates

line_trace.produce and line_trace.verify use indexed binary columns, an independent ordered triple (target,a,b) naming the three-space, and original forced positions. A transcript is JSON. The checker returns the proved Boolean or raises on invalid evidence. Successful checking invokes no native program, CMR Boolean, split solver, or matroid-intersection search. replay_controls.py runs all six stored decision variants with native process creation disabled.

## Initial and terminal checks

Reduce all named and optional columns modulo the span of the forced originals. A forced conflict proves NO by monotonicity of intersection. If the force already realizes the precise line, its physical support proves YES. When all names remain independent, failure of target membership in the full quotient ordinary span proves NO. Every YES independently verifies a physical support containing the original pins, whose span contains the target and whose quotient images of a,b are independent.

The initial carrier has six fresh ordered columns a,b,c,a+b,b+c,c+a, with c=target+a+b, followed by ordinary quotient columns in input order. Each step records a sorted retained set and an independent basis of at most two vectors for the full interface. Check that the six roots stay retained, each shore rank exceeds the order, the rank formula gives the asserted intersection dimension, and each interface vector belongs to both shores. Append all nonzero combinations as fresh labels after the retained positions. Each step strictly decreases rank and carrier size never increases.

A star terminal supplies two graph endpoints for each current labeled position, including loops and parallel copies. The stacked incidence/binary-matrix rank comparison verifies equality of both complete cycle kernels. The first three labeled edges must share a center with three distinct leaves. A graphic circuit is a simple cycle, a parallel pair, or a loop; none uses all three spokes.

## Negative soundness

Suppose a rooted circuit crosses a recorded split. Write A for its retained members and D for its discarded members. Both are proper independent subsets. Over GF(2), their sums agree at a nonzero vector w. Each shore spans w, so the replacement contains a fresh copy. Then A together with that copy is a circuit: A is independent and its unique expression for w uses every member. All three designated positions remain in A. Circuits wholly retained survive unchanged. By induction a rooted circuit in the original padded carrier would survive to the terminal graph, which rules it out. A physical exact-line witness before padding gives a rooted circuit by thinning to an independent subset summing to the target. The only terminal dependency in that support quotient is the full triple. Padding positions never count as physical selected columns.

This implication suffices irrespective of the order in which valid splits were chosen. A negative transcript needs no minimality certificates. The producer uses the [general three-elements algorithm](https://arxiv.org/html/2611.20960v1#S2) for completeness and polynomial-time generation. Its positive decomposition transcript additionally records common-independent-set certificates excluding lower-order splits and a terminal excluded minor. All positive results independently pass the original physical support check.

## Replay results

56 labeled physical instances agreed with exhaustive subset semantics, including all six decision variants, split orders 0,1,2, and eight rejected corruptions. The negative example has successive orders 0,1,2 and ends at a labeled star. All six decision types are saved in controls.json and replayed offline. Python checker evidence is separate from Lean artifacts. The prerequisites are the unmodified sibling three-name-backend and three-name-certificates directories on PYTHONPATH. No CMR executable is needed for replay.
