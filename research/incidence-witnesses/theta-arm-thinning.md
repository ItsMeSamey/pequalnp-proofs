# Physical removal by thinning positive arms

Start with one fixed full theta with k=q+1 arms, after any physical compilation preserving its singleton flags and its independent two-by-two negatives. Denote by L the previously booked removed slots relative to original size s; the intermediate has at most s−L slots. Each arm has three positive flags. For every intermediate raw or gate v, let A_v be the arm labels on whose flags it accepts at least once.

Choose j omitted arms S with 0≤j≤k−2. Mark v if A_v is contained in S, with indicator I_v. Set all marked signals to zero. Every surviving positive-flag evaluation remains unchanged by induction, and negative outputs only decrease. Both nonpole raws on every omitted arm are marked, leaving a theta with k−j arms. Each reader outside the marked set with a marked input is an OR with exactly one such slot and can be bypassed. Since A_OR is the union of its two operand supports, savings are at least
    R(S) = sum over gates v of I_v + sum over OR g=(a,b) of (I_a+I_b−2I_g).
Raw indicators enter only via operand slots. Count supports afresh on the actual intermediate after earlier savings; previously removed gates cannot contribute.

The remaining circuit needs at least 4(k−j) gates. Thus s≥L+4k+R(S)−4j. For uniform j-subsets put h(d)=choose(j,d)/choose(k,d), zero for d>j. The inequality holds with each I_v replaced by h(|A_v|), by expectation conditional on the original theta. One thinned theta realizes at least the resulting bound. For fixed preprocessing one may select j or use conditional expectation to obtain an explicit subset. No positive-witness multiplicities are counted as physical gates. Independently reviewed by /root/incidence/audit.
