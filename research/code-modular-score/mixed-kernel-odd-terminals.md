# One mixed root can impose unbounded odd-degree demands on a regular host

Use the reduced binary incidence matrix D of K_(m+1), relative to a distinguished center, with m≥3. Its columns are the m units (spokes) and all two-unit columns (rim edges). Set the one dual marker M to one on every spoke and zero on rim edges, so b=DMᵀ is the m-vector of ones. Give the single primal marker L the first row of D plus the indicator of one rim edge, so its restriction to ordinary cycles can be nonzero.

In the two-named-column representation

    [ D   0   b ]
    [ L   1   0 ]

a cycle with named coefficients (1,1) requires Dc=b and Lc=1. Every one of the m noncentral vertices must have odd degree in c, as must the center when m is odd. Thus no bound depending only on the two names controls the number of affine odd-degree terminals, even on a complete graphic reference. This named-kernel request is realizable: contract all m ordinary spokes and delete the ordinary rim edges. The sum of all spokes has D-image b and L-value one, so the two named columns become parallel and nonzero (the spoke D-columns are independent), giving exactly the kernel span{(1,1)}.

Adjoining the affine demand as an ordinary port is not guaranteed to yield a regular matroid. Contract the named identity column to get [D|b]. Contract all but three spokes, retain the three remaining spokes and the three rims among their endpoints, and delete all other ordinary columns. Together with b these are all seven nonzero binary columns of dimension three, giving the nonregular Fano minor.

These obstructions concern transferring the homogeneous common-forest proof unchanged or asserting regularity of the natural augmentation. They do not establish hardness or preclude alternative algorithms. The obstruction persists at fixed score and root dimensions and with a connected graphic reference.
