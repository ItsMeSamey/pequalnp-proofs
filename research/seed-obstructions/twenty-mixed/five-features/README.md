# Five point features serving two lines

Choose distinct residual lines T,U. Suppose an envelope on five monotone point features accepts each singleton of T, and rejects every T-active sampled negative whose point set meets all five other lines. Make the symmetric assumption for U, on the same features. Then at least one of the two four-point singleton masks has a point circuit of cost at most two on these features and the raw singleton bits. The two complete masks together cost at most five gates.

For feature i let its 13-bit mask list the point singletons where it is true. At a positive p and a relevant negative Q for that arm, some feature must contain p and miss all of Q. Otherwise the negative feature valuation dominates the positive one by monotonicity. A maximal Q implies the same restriction for every smaller Q.

The verifier encodes all five masks as Boolean unknowns and imposes these necessary separation constraints. A sufficient cheap expression for either star uses d=0,1,2 gates on the features, has no outside singleton, and contains at least 2+d of the four required singletons. Complete that star with at most 2−d raw ORs. The other star costs three raw ORs. For d=0 test the five features; for d=1 their pairwise ANDs and ORs; for d=2 combine a one-gate expression with a third distinct feature. Exclude every such cheap expression for both arms and test for unsatisfiability. The checker derives its inequalities directly from the pinned theorem at ../../eight-line-surplus/samples.py. It uses python-sat and CaDiCaL 1.9.5.

Run python verify.py for all 21 pairs. Optional --proof-directory DIR writes each DIMACS formula and its textual DRAT refutation. Run drat-trim DIR/01.cnf DIR/01.drat, and similarly for each pair, to check an individual proof.
