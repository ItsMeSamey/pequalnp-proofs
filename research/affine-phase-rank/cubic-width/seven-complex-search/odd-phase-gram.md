# Gram bound for weakly overlapping full complex chirps

For full nine-bit fourth-root chirps, a nonzero normalized overlap of modulus 1/sqrt(512) has phase an odd multiple of pi/4: the unnormalized Gaussian integer has norm 512 and is 16(±1±i). For r full columns with no pair sharing a signed nonidentity Pauli,

    lambda_min(Gram) >= 1−[cot(pi/(4r))−1]/32.

Write h(theta)=max_k cos(theta−(2k+1)pi/4), periodic of period pi/2. For any test vector with magnitudes w_i normalized by sum w_i²=1, the adverse Gram contribution scaled by sqrt(512) is at most sum_{i!=j} w_i w_j h(theta_i−theta_j). Zero off-diagonals only reduce that upper bound. Add the diagonal 1/sqrt(2), maximize jointly over weights and positions, and ignore zero weights. Coincident positive positions cannot maximize: split them into two groups with opposite velocities and zero weighted net velocity. Interactions with other distinct positions change only quadratically, while interactions between split groups increase linearly by the upward cusp of h at zero. Thus all positive positions are distinct.

Set P(x)=sum_i w_i h(x−theta_i). Weight stationarity gives P(theta_i)=lambda w_i. Position stationarity gives opposite one-sided slopes with jump sqrt(2)w_i, so the right slope is w_i/sqrt(2). Between positions P''=−P. Conservation of P²+P'² shows neighboring weights agree. Equal endpoint heights and opposite slopes force each interval length 2 arctan(1/(sqrt(2)lambda)). Hence positions are equally spaced, lambda=cot(pi/(4r))/sqrt(2); subtract the diagonal. If fewer positions were used the bound is smaller. The case r=1 is immediate.

At r=7 this gives lambda_min >=0.75389, strictly above 3087/4096=7(21/64)^2. The exact comparison follows from cot x<1/x−x/3 for 0<x<pi/2 (differentiate sin x−x cos x−x² sin x/3) and pi>3.141. Combined with the full-chirp fidelity gap, a seven-full dictionary with no signed stabilizer shared by any pair must include a maximum-fidelity product atom. This does not rule out arbitrary seven-full lists.
