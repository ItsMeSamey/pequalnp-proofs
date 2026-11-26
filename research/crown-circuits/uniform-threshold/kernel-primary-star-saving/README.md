# Star pin for primary size minima

ThresholdNativeStarSaving.star_saving_primary constructs a k-input threshold-two circuit D at a hub of an eligible regular globally size-minimal circuit C. When the hub has k ≥ 2 incident inputs and the forced hub activates t other shared hubs, D.size + (2n − k) + t + 1 ≤ C.size. The regularity assumption is on this same physical circuit. The proof uses size minimality without a secondary singleton-count minimum.

The source imports ThresholdNativeStarSaving from research/crown-circuits/uniform-threshold/kernel-star-cap, immutable commit 895290a1b6a334a1f430f5be77f956e6588d48a1. Compile in its pinned Lean environment with its module closure on LEAN_PATH. The compiler receipt records the three standard axioms of the endpoint.

For a regular size-34 fourteen-input candidate, the separate bound C(14) ≥ 34 establishes primary minimality. With the established small-input minima, the permitted t maxima at k=2,3,4,5 are 6,4,2,0. Degrees six and seven are excluded by monotonicity and C(6)=13, eight and nine by C(8)=19, and larger degrees by the 2k−4 OR floor. This finite specialization is a mathematical consequence of the compiled star inequality and those numerical inputs.
