# Counting uncovered endpoint colorings in fixed-parameter time

Each supplied physical route has a single affine activation system. Inside the affine domain prescribed by the virtual endpoint equations, uncovered potential assignments have count

sum over J⊆[P] of (−1)^|J| times the size of the solution set of the endpoint equations and all route equations in J.

This follows by expanding the product of the indicators of failure. Gaussian rank returns each intersection size as zero or a power of two. Numerators have O(2|V|+P) bits including partial sums. Time is 2^P poly(total explicit input), independent of individual route lengths in the exponent, and space is polynomial by iterating subsets. An uncovered potential is recovered by repeatedly pinning one coordinate and testing positivity. P=0 and empty/singleton endpoint domains obey the same formula. Use on supplied candidate routes after checking their indexed physical incidence boundaries. This elementary affine union computation improves the product-of-route-lengths verifier when the number of routes is the parameter.
