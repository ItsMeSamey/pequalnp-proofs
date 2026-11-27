# Unbounded rank of every two-shore certificate, for every compatible chart

Use m≥1 triples of passive sockets (i,0),(i,1),(i,2), each with its own independent rotation τ=(012). Let S exchange (i,2) with (i+1,0) at each of the m−1 joins. All these exchanges have disjoint endpoints. Set fixed feedback to S after the product of one fixed τ on every triple. Mark (1,0) and (m,2). The return for any physical setting s is F=S after the local permutations τ^(1+s_i). These local permutations are all three-cycles. Before S there is one orbit on each module. Each successive transposition joins the prefix orbit to the next module. Thus every setting yields a single orbit, and the roots always meet.

Choose any compatible rotation chart. Its black baseline is some s and its white baseline the complementary setting, so each has precisely one disk. The chart has genus m by Euler's formula. In socket labels gauged to the chosen black transition its feedback is F as above and its other local transition at gate i is R_i=τ^(1−2s_i). We claim every pair of exclusive black and white binary chains with the prescribed root boundary and nullhomologous closure has support cycle rank m. Adding the private terminal spokes does not affect cycle rank.

## One binary cocycle for each gate

Use the triangular subdivision from check_two_shore_homology.py. At socket a the coordinates I_a,O_a are the wire halves incident to the switch; b_a,w_a are midpoint-to-disk edges; B_a,W_a are black and white incidence arms at that switch. The two black triangles have edges (I_a,b_a,B_a) and (O_a,b_{F a},B_a); the two white triangles have (I_a,w_a,W_a) and (O_{R a},w_{F R a},W_a). All arithmetic below is binary.

Fix gate j. Define socket values r equal to zero on modules before j and one beyond j. At j put r(j,0)=r(j,1)=0 and r(j,2)=1. The neck transpositions exchange sockets with equal r. Therefore the sum of r_a+r_{F a} over each triple is zero. Choose numbers W_a on each triple satisfying

    W_a + W_{R⁻¹a} = r_a + r_{F a}.

A three-cycle has exactly the even-parity vectors in the image of this difference operator. Away from gate j the right side is identically zero, and take W_a=0 there. Set B_a=r_a+W_a. Define the binary cochain with arm values B_a,W_a and other values I_a=O_a=B_a, b_a=0, w_a=r_a. Its sum around every triangle is zero by the displayed equations, so it vanishes on all nullhomologous closed chains. The two root transversals, using b,w at the marks, sum to one since the outermost r values are zero and one.

At every switch the support of each color uses an even number of its three arms, hence zero or two. Outside j the values of the cochain are constant on all black arms of a given switch and also on all its white arms. All such contributions vanish. If gate j were unused the closed certificate would evaluate to one, contradiction. Applying this separately to every j forces all m switches to be used.

Each used switch takes exactly two arms of one color by exclusivity. Those arms join it to the unique global disk of that color. They form a two-edge graph cycle, and edges of different switches are disjoint. The support cycle rank is consequently exactly m. Positive certificates do exist by the two-shore criterion, since every physical mask joins the roots. The statement holds for every compatible choice of native port rotations and also if the physical witness mask is prescribed. It concerns certificate support rank in the two-shore formulation, not the difficulty of recognizing these inputs: here every mask already has one orbit. The example allows high-degree facial disks. Its genus grows with m and the example forces rank m within the 2g general upper bound.
