# Recovering even majority by adding one input

Let q be even, a_i an unknown binary dual basis, and χ_a(x)=(−1)^{a·x}. For either prescribed choice c∈{−1,1} on ties, the clean hidden majority is

    f(x) = sign(c + Σ_{i=1}^q σ_i χ_{a_i}(x)).

From any supplied membership oracle for f, form the (q+1)-input oracle g(x,z)=(−1)^z f(x). Its clean version equals odd majority of the q+1 signed frequencies e_z and (a_i,1), with signs c and σ_i, respectively. Those frequencies are linearly independent by projection onto the original q coordinates. Each corrupted x causes just two corrupted inputs of g. Apply the [odd deterministic recovery algorithm](hidden-affine-majority-deterministic.md); the dimension increase costs a constant factor in its stated exponential running time.

In the recovered signed top list the extra frequency is the sum of those q+1 basis frequencies. Its last coordinate is one since q is even. For q≥4 its projection to the original coordinates is nonzero and distinct from each a_i; e_z is the only frequency that becomes constant at z=0. Keep e_z and omit any other top frequency. The odd theorem says the resulting signed majority computes g exactly. Restrict z=0: the surviving constant has sign c and the other q frequencies project to a basis, since they are independent together with e_z. This recovers an exact even-majority presentation with the correct tie convention. The finite small dimensions require the same identifiability convention under errors as the odd theorem. No hidden affine map is needed to construct the lifted oracle.
