# A pure pin outside a tight star saves an OR

Consider a live, constant-free binary AND/OR circuit for threshold two with two OR-reader occurrences per raw. Flatten each single-use OR with an OR consumer. Let U be a pure group of degree k≥2 with d pure neighbors in the simple raw-incidence graph. Let r be the sum of t−1 over mixed groups, where t≥1 counts the nonraw slots. If there exists a pure vertex C outside U and its neighbors, then the k-edge star threshold has a circuit with at most r+k−d−1 OR gates.

Start with a formal input for every pure-group output. Keep the k−d raw star edges at mixed groups. Set all other mixed raw slots false. The injections occur at distinct mixed groups by simplicity. Rebuild every mixed group as the binary OR of all its original t nonraw slots and its retained raw input, if present. Use a wire when only one slot remains. Keep every AND and the original output; no other simplification is needed. This costs at most r+k−d ORs.

Every pure-group output still has a path to the output. Take an original path from the pure group. It never enters a raw input or another pure group, and each mixed group is entered by a nonraw slot. The rebuild retains a path from each such slot to its output, of length zero for identity groups. The unchanged ANDs retain their operand slots. This proves physical occurrence even if the independent pure pin were semantically inessential.

Set only the outside pure pin C to false. On a surviving path propagate false through ANDs to its first OR, and bypass that OR to its other operand. Such an OR must exist: an all-AND path, including a zero-length path, would force the entire output false whenever C is false. Yet the nonzero star below is compatible with C=false. This saves at least one OR.

Finally set U=true, its d pure neighbors to their respective individual raw star variables, and all other pure vertices to false. The k−d mixed injections are the other star variables. Nonempty assignments now agree with the physical circuit; the empty assignment rejects by monotonicity and singleton rejection. Thus threshold two on k inputs uses at most r+k−d−1 ORs.

For the five-pure-group seven-AND case with quartet U on the triangle and two isolated pure vertices, r=2, k=4 and d=2. Either isolate is outside the star. The bound is three ORs, while threshold two on four inputs needs four. The conclusion holds for either placement of the doubleton.
