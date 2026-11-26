# A singleton boundary in a minimum monotone circuit

Let C be a globally minimum-size monotone AND/OR circuit with binary gates for its specified Boolean task. It suffices that replacing it by any smaller circuit with the same full Boolean function contradicts minimality. Delete dead gates, constant gates, unary identities and repeated-input gates. The same conclusion therefore applies to a minimum circuit on a promise whenever these elementary simplifications and the construction below are admissible. Gates can share outputs freely. Count fanout by operand occurrences, including each use of the same signal by different consumers. Fix a raw input x such that the circuit output is false on the assignment e_x which sets just x to true. Call an internal wire hot when it is true on e_x, and cold otherwise.

Let f_x be the number of operand occurrences of raw x, and B_x the number of operand occurrences whose source is hot and whose consuming gate is cold. Here raw x is a hot source. Every boundary occurrence enters an AND whose other parent is cold. Let d count the boundary occurrences whose source is raw x itself.

**Boundary rerouting theorem.** In this model B_x ≥ f_x.

An AND directly reading x that is hot on e_x would compute precisely x: its other operand is true whenever x is true, by monotonicity. Such a gate could be bypassed in a minimum circuit. Every one of the f_x−d remaining raw-x operand occurrences therefore belongs to a hot OR of the form x∨T. These occurrences designate f_x−d distinct gates, because repeated operands were removed. Mark those gates for omission. Leave intact the d raw-x occurrences that feed cold ANDs.

Build a new circuit in topological order, assigning a replacement wire to each original wire. At a marked gate x∨T, assign the current replacement of T as the gate's replacement, and emit no gate. This also defines the replacement when T was produced by another marked gate. At every other gate, use the current replacements of its original parents. For each operand occurrence whose original source was an internal hot wire and whose original consumer was cold, insert an OR of that source's replacement with raw x, and use its output in this operand position. This classification uses the original circuit and e_x throughout. One may pay for a separate OR at each original boundary occurrence, even if the original source was shared, omitted, or replaced by the same signal as another source. The consumer of a boundary occurrence is cold and therefore was never marked for omission. Emit the original gate operation with the resulting operands. Return the replacement of the original output.

For an arbitrary input assignment with x false, induction on the original topological order shows that every replacement has the original value. Each omitted OR equals its other operand, and each inserted OR equals its replaced input.

For an arbitrary assignment with x true, every originally hot signal has original value true by monotonicity. Inductively compare only originally cold gates. Their originally cold operands agree by induction, with unchanged raw values as the base. An originally hot raw operand is x and is passed through unchanged. An originally hot internal operand is forced true by the inserted OR regardless of its replacement value. Thus every originally cold gate returns its original value, in particular the specified output. The proof makes no claim about intermediate replacements of originally hot signals on these assignments.

The new circuit omits f_x−d gates and inserts B_x−d gates, for size at most |C|−f_x+B_x; further simplifications are optional. Global minimality gives the inequality. Terminal normalization or secondary minimization of the number of dirty ANDs is unnecessary. The construction can leave a terminal-normal subclass, so minimality restricted only to that subclass would not suffice without a size-preserving normalization theorem.

**Exact edge count.** Let D_x be the number of ANDs true on e_x, J_x the number of ORs whose two operands are true on e_x, and f_g the physical fanout of internal gate g. If H gates are hot then H+D_x+J_x edges enter hot gates from hot sources: one per hot gate and an additional edge for each hot AND or two-hot-parent OR. The hot sources emit f_x+Σ_hot g f_g operand occurrences, exactly B_x of which enter cold gates. Therefore

    D_x + J_x + B_x − 1 = (f_x − 1) + Σ_hot g (f_g − 1).

Here subtraction is ordinary integer subtraction. The identity holds without minimality and also when x is unused. Since the output is cold, a live hot internal wire has fanout at least one. The rerouting theorem gives, for each x separately,

    D_x + J_x ≤ Σ_hot g (f_g − 1).

In particular, f_x≥2 implies B_x≥2. A hot AND on x requires an internal hot wire that genuinely branches. Summing over x counts each shared internal gate once for each singleton on which it is hot. An injection of all dirty ANDs into the unweighted physical fanout surplus would require an additional argument.

**Distinct-source refinement.** If H is the set of distinct internal hot wires with at least one cold consumer, reuse a single inserted OR per member of H on all of its original boundary occurrences. The replacement of that source is already available before each of its consumers. The same construction then gives f_x ≤ d+|H|. Thus the edge ledger can also deduct Σ_{g∈H}(b_g−1) from its upper bound on D_x+J_x, where b_g is the number of cold operand occurrences originally supplied by g.
