# No minimum size-19 six-AND threshold-eight circuit has exactly one dirty AND

Here dirty means true on at least one raw singleton. The six-AND physical circuit has thirteen ORs and size nineteen, the absolute eight-input minimum. Collected-clean normalization preserves every retained AND's singleton trace and cannot delete an AND at a size minimum. Five comparators are clean terminal terms; the remaining dirty comparator has nonempty continuation W on their signed operand pins. It cannot reach both signs of any clean comparator since some singleton triggers it. Relabel the clean comparators and swap signs to make W the first positive pin in each of w=1,...,5 axes.

For nondirect circuits transpose the OR diagram as in geometry/ten24-six/RESULT.md and algebra/tenseven/one-dirty.md. Here the thirteen ORs include four collector gates, and the nine-gate front carries nine sources (eight raws plus the dirty output) to twelve comparison operands. The reverse bank has at most 9+12−9=12 unions. Each nonliteral raw receiver needs an independent terminal join because the raw masks are incomparable; no raw is contained in W (otherwise it is hidden whenever the dirty comparator is activated by another singleton). Thus at most four helper joins remain, including the construction of W. Each raw is available as a union of two bank wires; the six comparison axes include the two input signs of the dirty gate. An input setting that contains both its signs also provides W; rejection then means no clean axis occurs with both signs.

The frozen t8-one-dirty.cpp is the original geometry/ten24-six/onedirty.cpp with just n=8, dh=4 replacing n=d+4,dh=n−5; run with d=6. All other clause, helper ordering, symmetry, volume and incompatible-receiver selection logic is identical to the prior model. Consistent helper joins building W may be ordered first; thereafter every receiver join is tested. Superset dominance among consistent candidate receivers preserves pair conflicts and the requirement of an actually dirty singleton. No positive choice of eight mutually conflicting receivers was found. The counts below list visited bank nodes and compatibility fronts.

| w | bank nodes | fronts |
|---|---:|---:|
|1|23,524|22,980|
|2|3,439|3,416|
|3|531|523|
|4|111|68|
|5|131|4|
|Total|27,736|26,991|

To replay, compile t8-one-dirty.cpp with a C++20 compiler and run the binary separately with arguments w and 6 for w=1 through 5. Raw receipts are one-dirty-width1.log and one-dirty-width2-5.log.

There can be at most one direct (one-signed-pin) raw in any threshold instance of arity at least three. A direct raw x must be the sole source of its signed pin: if another singleton already enables that pin, adjoining x changes no AND or output. Its comparator therefore cannot be dirty (x alone reaches only the one pin). This clean terminal is the only possible new acceptance in a pair containing x, so any other singleton supplies its opposite sign. If y were another direct raw, y alone fires no comparator and its only pin must be that opposite sign. For any third singleton z to pair with both x and y, it would then have to supply both signs of this same clean comparator before either addition. That would accept z, impossible.

If a one-dirty T8 candidate has a direct x, delete its clean comparator, one collector OR and the root of its opposite operand, the maximum of the remaining raws, as in geometry/ten24-six/RESULT.md. This produces T7 with at most 16 gates. Since 16 is its absolute minimum, exactly these three gates disappear, leaving five ANDs. The dirty singleton survives: x itself had no activated comparison and every other singleton still has the original remaining gate values. If the seven-input circuit now has a one-pin raw choose it, otherwise choose any raw. Split the chosen raw into the disjunction of two fresh labels and append the AND of those two labels to the output collector. This restores T8 at 19 gates with six ANDs and the single original dirty comparator; singleton traces are inherited, and the new comparator is clean. Each replacement raw's formal mask is the original mask plus one new sign on the split axis. Every unchosen mask is unchanged. Since the smaller circuit had at most one direct raw and it was chosen if present, all eight new masks are nonliteral. This contradicts the nondirect census.

Together with single-level-extremal-cover.md and signed-cover-extension.md, any eight-input minor obtained by deleting a branching pure doubleton from a putative T10/24/A6 circuit must already have at least two singleton-hot ANDs. The computation is a source-level finite enumeration and does not enumerate circuits with two or more dirty ANDs.
