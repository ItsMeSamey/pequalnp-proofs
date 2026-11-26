# Equality rank with two pins and private clause coordinates

Let indexed binary columns x span V of rank r. Each carries a permitted two-bit value o. A linear function H from V to F₂² must respect prescribed values on a d-dimensional pin space U. The equality objective asks that the x with H(x)=o span V. Every repeated column retains its own label.

## Why independent rank losses cannot accumulate

Choose any indexed basis of V/U from the physical columns and assign H their required labels together with its prescribed values on U. This always activates r−d independent columns. Hence at d=2 every NO instance has optimal activated rank either r−1 or r−2. An attempted reduction in which each unsatisfied clause costs its own independent rank direction for every pinned H fails on three disjoint unsatisfiable clause blocks. One explicit 3CNF block contains all eight signed clauses on three distinct variables, falsifying exactly one clause on every assignment. With three copies on fresh variables, every assignment falsifies precisely three clauses.

Cardinality has a different behavior even on concrete incidence inputs. For each edge uv of a graph use column e_u+e_v with label (1,0). Any assignment H activates at most the cut chosen by its first coordinate, and taking its second coordinate zero attains that cut size. Thus maximum agreement cardinality is precisely MaxCut, whereas one can activate all edges of a spanning forest by choosing its bipartitions. To retain two prescribed pins, add two independent directions with a column whose label matches the prescribed pin at each. This shifts the optimum count by two and preserves full rank in every instance.

## Exact solver for private blocks of bounded rank

Use a supplied direct-sum presentation V=V₀⊕V₁⊕...⊕V_m. Suppose the physical columns inside V₀ include a set that actively spans V₀ for every base map H₀; a basis with all four labels at each direction suffices. Every other column belongs to V₀⊕V_j for a single j. Write it as a+v and allow arbitrary labels, arbitrary couplings a to all base coordinates, and arbitrary pins mixing all the subspaces. Write n=dim V₀ and b=max dim V_j. In the usual clause layout V_j is a single private clause coordinate and the alternatives are c_j+a with one per literal.

For fixed H₀, enumerate each local map H_j (at most 4^b choices). Test whether the v among label-agreeing columns span V_j. Keep a local map for each resulting 2d-bit contribution to the d pin values. Combine the local tables by set addition, retaining a predecessor. Add the fixed H₀ contribution. This decides whether H₀ extends. Indeed, active base columns already span V₀ and the projected private spaces form a direct sum.

Only a polynomial list of base maps needs testing for fixed d. Choose a fixed basis of V₀, setting any arbitrary default color at each. Given an unknown witness, select a projected active basis in every V_j. The labels on this basis uniquely specify H_j as an affine-linear function of the entire H₀. With these same selected indices, all 2d output pin bits together become an affine-linear function of H₀. The difference from the all-default pin output is a sum of individual variable contributions in F₂^{2d}. A subsystem of at most 2d of these contributions sums to that same difference, by taking a basis from the differences and solving. Use the original variable color on just the subsystem, and the default elsewhere. Reconstruct H_j on the selected indices. All chosen local bases still agree, and the pins are restored.

Enumerate at most 2d nondefault variables and their colors, and run the local tables for each choice. At d=2 the resulting time is O((n+1)^4 4^b poly(input)), regardless of the number of clauses. For b=1 the local values are directly the allowed colors o+H₀(a). In particular, when the pins see only the base, each private clause can always activate an option by choosing its own clause-coordinate value.

There is also an exact transversal variant. Give each base variable a nonempty unary domain and require some label-agreeing singleton at that variable in addition to the projected local bases. Defaults and original colors can both be taken within their domains, so the proof is unchanged. This requirement is stronger than arbitrary full equality rank for non-full unary domains. For example take independent v,c,p with pins H(v)=01 and H(p)=00, singleton labels (v,00),(p,00), and alternatives (c,00),(c+v,01). Choosing H(c)=00 gives full activated rank via the two clause alternatives and p. The variable singleton cannot be used. This is the specific mechanism by which a construction may evade the transversal obstruction.

## Grouped allow-lists

For each distinct physical column x, collect its set O_x of available labels. If it has three labels, equality on some copy is equivalent to avoiding the sole missing value. A four-label group always activates and can be encoded by two unequal-value tests with different forbidden values. Let q be the rank modulo U of the columns with at most two distinct labels. Enumerate the 4^q extensions on their collective span together with U. On each branch these small-list columns are either inactive or always active. Discard inactive columns, check whether the retained physical columns still span the original V, and evaluate the remaining forbidden-value tests using the pinned unequal-label algorithm with at most d+q pins. The total time is 2^{O(d+q)} poly(input). [Binary unequal-label algorithm](../binary-aggregate-selector/README.md)

## Scope and executable controls

Run python check.py. Its one-coordinate block implementation agreed with whole-map enumeration in 250 small dense two-pin cases, 102 of which were feasible. An extra unary-domain instance needs all four permitted nondefault variable colors simultaneously, so the four-exception bound can be tight for this algorithm.

These arguments give restrictions on local SAT encodings and algorithms on the stated hosts. The general two-pin, two-bit equality-spanning problem with unrestricted columns and offsets remains open in this audit.
