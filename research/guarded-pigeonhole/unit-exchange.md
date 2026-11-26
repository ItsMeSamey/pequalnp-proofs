# Exchanging individual Boolean pins in both directions

Engine P is GF(2) PC of bounded degree on native guarded polynomials. Engine R is bounded-level SA or bounded-degree real quadratic-module SoS on the direct forbidden-assignment CNF. Either engine can refute or certify a unit, including by refuting its opposite restriction. A certified unit is substituted into both encodings, which may be rebuilt. The family below defeats arbitrary repeated exchanges at sufficiently small linear budgets.

## Two charged switches

Take a balanced simple bipartite core obtained by superimposing eight permutations on n+n vertices and collapsing parallel edges. Choose permutations for which every s-set of left vertices, 1<=s<=gamma n, has more than 6s distinct neighbors. The probability calculation in the [base graph construction](README.md) before deletion proves existence. Each such set has more than 4s unique neighbors by counting the original 8s half-edges. Every core edge belongs to a permutation perfect matching. Use the first permutation as reference matching. Add an unmatched pigeon u with edges e1,e2 to different holes. At each hole, order the reference edge first, and the unmatched edge last if present. Compile the resulting marked FPHP as in the [base graph construction](README.md).

Use a separate bounded-degree edge expander H_j with m proportional to n and root r_j for each j=1,2. Write x_j for x_{e_j}. XOR a_{j,r_j} into the alternate of row e_j. Add guards

    a_{j,v} (sum_{f incident to v} z_{j,f} + [v=r_j] x_j) = 0,
    z_{j,uv} (a_{j,u} + a_{j,v}) = 0.

Every fresh coordinate has one pivot. The sole marker is x_1+x_2=1, all row and column weights are bounded, and maximum hidden deficiency equals one. Summing the rows of H_j gives x_j a_{j,r_j}=0 identically over GF(2). Adding this quadratic consequence to the modified e_j row recovers its original guard. Thus the system is unsatisfiable and degree-two guarded-consequence import followed by the old LP refutes it.

## Every single pin retains PC hardness

After forbidding an old edge (delete it) or selecting it (delete its two endpoints), every surviving s-set in the small-set range has at least s unique neighbors. A set of k core pigeons, k>=1, begins with at least 4k+1 unique neighbors. Adding u to the set costs at most two, and the edge or hole deletion costs at most one, leaving at least 4k-2>=k+1. Deleting a pigeon outside the tested set has no effect. For the singleton u at least one of its two neighbors remains.

Set all fresh coordinates zero to recover the marked base. To pin an old residual coordinate to zero, restrict the corresponding source FPHP edge variable to zero. Source FPHP reduces to the graph with the edge removed. To pin the coordinate to one, select its edge, fix all other adjacent edge variables to zero, and delete its endpoints. Source axioms now reduce to zeros or axioms of the smaller FPHP, including the pigeon existence clauses. Apply these constants to the source-to-network PC simulation. A degree-d proof on the pinned target would give a degree-max(d,O(1)) proof on the residual graph, which still has one more pigeon than hole and retains the boundary expansion above. The Miksa–Nordstrom FPHP theorem gives linear required degree. Expanded PCR size likewise retains its exponential bound.

For either value of a z coordinate take all a zero, leaving z arbitrary and the hard base intact. For a new a=0 take all gadgets zero. For a new a=1 take all a in that gadget one, all its z zero, and its x_j zero. Set all other fresh bits zero. This leaves precisely the hard x_j=0 restriction of the base.

## Every single pin retains real local feasibility

Choose any core perfect matching M and encode its residual core edge bits. The affine reconstruction of each reference edge agrees with M, because exactly one edge per core pigeon is occupied. Add exactly one unmatched edge e_j. This leaves the affine reconstructions unchanged. The only violated original guard is e_j, since it is last at its hole. Set all a in gadget j one, and all a in the other gadget zero. The shift corrects e_j. Inactive z bits are arbitrary. The remaining constraints are odd-charge Tseitin on H_j. The linear SA and SoS witnesses from the [compatible marginals](expander.md) and [positive moments](sos.md) extend with these constants.

For an old residual core edge pinned to one, select a permutation matching containing it. For zero use the reference matching, which avoids every residual edge. For x_1 or x_2 select which unmatched edge to add. For an a pin choose its gadget active or inactive. For a z pin choose its gadget inactive and assign the desired value. Thus every individual pin preserves feasibility at the stated linear budgets.

Each engine remains feasible under either value of every coordinate. Neither can obtain the first unit, even by testing the opposite restriction. Unlimited rounds of unit exchange therefore stall. The result concerns unit-only message passing. Importing derived quadratic guards restores the two old rows in degree two and exposes the old LP refutation.

[Finite two-switch checker](check_unit_exchange.py).

[The symbolic restriction checker](check_unit_restrictions.py) also verifies the charged sums and the residual source proof simulations for all 68 single-literal restrictions of the finite example.
