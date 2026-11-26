# Truncating reverse contexts at the collision region

Give every wire its syntactic set of raw query labels. A collision occurs at an AND when its two children's query-label sets intersect. Assume the UNION of those sets has at most d labels at each collision. Let H contain those ANDs and their entire internal input ancestry. Every gate of H then has at most d labels. The result below does not follow from bounding the intersection alone. Assume d<N; the output cannot belong to H, since all N query inputs are essential. Write h=|H| and v=s−h. Let b count distinct H signals feeding the v-gate outside circuit, and e count distinct raw query variables occurring directly outside. The outside gate graph and its inlets are connected and binary, so b≤min(h,v+1−e).

Compute every baseline at zero query (at most s gates). For each H signal g compute its exact singleton specialization for each query label in its scope. A child lacking that label contributes its baseline. Let C consist of the H gates with a syntactically query-only parent, including a raw query as such a parent. Every such parent is constant at any singleton query, so computing the corresponding gate costs nothing after constant folding. The cost of this stage is at most d(h−|C|).

Outside H propagate reverse contexts from the output, stopping at H boundary wires. OR passes its received context to both operands; AND passes to each the context conjoined with its sibling baseline. Aggregating multiple incoming contexts costs at most v+1−b−e, since the v exterior gates send 2v total contributions and v−1 exterior internal wires, b boundaries and e query inputs each receive at least one. Payload contributions can be omitted. Thus reverse propagation costs at most 3v+1−b−e gates.

For each boundary signal g, and query l in its scope, emit its exact specialized value AND its outside reverse context. Every raw query context contributes one additional term to its label's output. These are sound for arbitrary payload data: a successful context supplies a path to the scalar output with true baseline siblings at every AND. They capture every positive flag on its selected query l. In a true parse at that flag, no query-free root parse is possible, since the payload singleton alone is negative. At each outside AND only one selected branch can use l: otherwise its child scopes intersect, making it a collision in H. The parse therefore reaches one raw l or a boundary gate carrying all occurrences of l, and every other sibling on the path has a query-free parse.

Let b_p denote the number of purely query-dependent boundary signals in the syntactic sense. Their specialized bits are constants. The boundary products therefore cost at most d(b−b_p). Joining the terms across all labels costs at most db+e−N: every query must have at least one term by the positive flag coverage just proved. The resulting N outputs meet the simultaneous sparse-query lower bound. Under the original promise, singleton point queries require correctness only on line masks through size q, exactly the theorem's stated requirement.

Finally |C|+b_p≥N−e. Each query variable with no direct outside use starts in H. Choose one path from it, continuing through pure-query H gates by a single preselected successor for each encountered pure signal; stop at a pure H boundary or at the first mixed H consumer. There are at most b_p plus the number of these mixed consumers as distinct terminal roots. Each selected pure H gate can merge at most two paths and every mixed terminal gate has only one pure parent. Thus the number of distinct sources is at most the number of selected pure H gates plus the number of roots, which is bounded by |C|+b_p.

Adding the gate budgets yields

    Nq ≤ s+dh+3v+(2d−1)b−d(N−e)−N+1.

For d≥4 this is at most

    (3d/2+2)s−(d+1)N+(3d/2−1)+(2−d/2)e.

Indeed substitute b≤min(h,v+1−e) and v=s−h; the resulting piecewise linear upper bound is maximized when h=(s+1−e)/2. At q=401, any circuit with s≤646424 and every collision scope of size at most 78 satisfies the assumptions with d=78. The last upper bound is at most 64,189,535, strictly below Nq=64,642,403. Thus a hypothetical below-target circuit must have an AND whose two child scopes overlap and whose full union in this orientation exceeds 78 labels.
