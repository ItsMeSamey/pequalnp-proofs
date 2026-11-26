# Exact size for 12-crown endpoint banks followed by a formula

**Theorem.** Assign twelve distinct labels to the edges of a simple undirected graph. Compute zₑ = xₑ ∨ yₑ for each edge and the OR of its incident z-signals at each incident vertex. Feed the resulting vertex signals into any binary monotone AND/OR formula. Computing inequality on one-hot x and y requires at least 41 gates in this architecture. The 3-by-4 grid attains 41. The formula can have arbitrary depth, and a bank signal can occur in multiple leaves. The formula's internal gates have a single downstream use.

## Cost and zero certificates

There are twelve pairing gates. For s incident vertices, their banks cost Σᵥ(deg(v)−1) = 24−s gates. If the formula has L leaves, its cost is L−1. A 40-gate circuit would therefore satisfy L−s ≤ 5.

Give every AND node of the formula an independent fair binary choice. A zero certificate traverses both children of an OR and the chosen child of an AND. It succeeds when every reached leaf is false. A successful certificate exists precisely when the formula is false. A true subtree has success probability zero. Probabilities multiply at OR nodes because their children have separate internal choices. At an AND node the probability is the average of its children's probabilities.

On any false assignment with m true leaf occurrences, the probability of success is at least 2 raised to −m. This follows by induction. At an OR both children are false and their exponents add. At an AND with both children false, their average is at least the bound for the sum of their true-occurrence counts. With exactly one child false, choosing it costs one fair bit, and its true sibling contains at least one true leaf occurrence. The leaf case is immediate.

For each label e, use the event of successful zero certificates when that label is selected on both sides. Two such events are disjoint. A common successful certificate would avoid the true leaves for both labels and hence for their union, contradicting the positive distinct-label test.

An endpoint with zero occurrences can have only degree-one neighbors. Otherwise the corresponding singleton visible vertex set is contained in another edge's visible vertex set, and the union of the two is indistinguishable from the latter label alone. Split the unused vertex into private leaves for its edges, which weakly decreases the bank cost. On an isolated edge both endpoint signals equal zₑ, so two or more occurrences can be divided between them. Any remaining isolated edge with an unused endpoint has one true leaf occurrence on its equal-label input and occupies at least half the certificate space. At most one such edge is possible. We thus need to exclude twelve labels with occurrence surplus at most five over represented vertices, or eleven labels in at most half the space with represented-vertex surplus at most six.

## Coarse volume bounds

A heavy vertex has dᵢ ≥ 2 formula-leaf occurrences. A light vertex has one. A light–light edge has certificate measure at least 1/4, so there are at most four. A heavy–heavy edge ij has measure at least 2 raised to −(dᵢ+dⱼ). A heavy–light edge at i has measure at least 2 raised to −(dᵢ+1).

At most two heavy–light labels can use a given heavy vertex. If three did, fix that heavy signal to true and all other signals to false except its three corresponding light neighbors. Single light neighbors must be rejected and every pair must be accepted. Monotonicity then forces majority of three. The restricted formula uses each of these variables at most once. After constants are simplified, its root splits the three essential variables into two nonempty disjoint sets, one of which is a singleton. An OR root would accept that variable alone, and an AND root would reject the opposite pair. Both contradict majority.

For each nondecreasing heavy-weight profile with Σ(dᵢ−1) at most the applicable surplus, form one slot for each unordered heavy pair, two slots at each heavy for heavy–light labels, and four light–light slots. Sum the twelve or eleven cheapest applicable measure bounds. This excludes all eleven-label cases. The only twelve-label profiles whose coarse sum is at most one are (2,2,2,2,2) and (2,2,2,3). These sums use all possible heavy pairs.

## Deepest AND choices

Every used leaf occurrence has an AND ancestor. Otherwise its all-OR path to the root would accept an equal-label input incident to its vertex. At each occurrence impose the choice at its deepest AND ancestor that takes the sibling branch. Let Bᵥ be the signed Boolean subcube defined by all choices imposed by vertex v. Opposite demands on a coordinate make the subcube empty. If a certificate belongs to Bᵥ, it cannot reach any occurrence of v.

Call a selected label uv clean when Bᵤ ∩ Bᵥ is nonempty. Its intersection lies inside the label's zero-certificate event. Thus the cores of distinct clean labels are disjoint. For a label whose intersection is empty, some AND receives opposite demands. Its two children each have a true leaf connected to that child by an all-OR path, so this AND subtree is true and contains at least two true occurrences. Replace it, for this assignment, by a single true leaf. Its success probability is still zero and the success probability at the root is unchanged. The total true-occurrence count falls by at least one. The probability bound for this label therefore doubles.

Form a conflict graph on the heavy vertices with nonempty Bᵥ by joining two whose signed demands disagree. Each clean heavy–heavy label extends to a maximal independent set. Distinct clean labels cannot extend to the same set, since all demands in an independent set are simultaneously consistent. An h-vertex graph has at most M(h) maximal independent sets, where M(0)=1 and M(h) is the largest of (d+1) M(h−d−1) over 0 ≤ d < h. To see this, take a vertex of minimum degree d. Every maximal independent set contains a vertex u in its closed neighborhood. Removing u gives a maximal independent set on the vertices outside the closed neighborhood of u, of which at most h−d−1 remain. The bound is nondecreasing and gives M(4)=4 and M(5)=6.

A heavy vertex touched by a clean heavy–heavy label has at most one clean heavy–light label. Indeed, each clean heavy–light core at i occupies at least half of Bᵢ because its light endpoint imposes one binary choice. Two such disjoint cores leave no room for the nonempty clean heavy–heavy core in Bᵢ. Consequently the second heavy–light slot at each touched vertex receives the doubled bound.

## The final count

Choose the set G of exactly the clean heavy–heavy labels, with |G| ≤ M(h). Charge their ordinary bounds. Each other selected heavy–heavy label receives twice its ordinary bound. At touched vertices double the second heavy–light slot. Complete the twelve labels with the cheapest remaining slots. The following minima are grouped by |G| in increasing order. The verifier uses exact fractions.

| Heavy weights | Subsets checked | Lower bounds by number of clean heavy pairs |
|---|---:|---|
| 2, 2, 2, 2, 2 | 848 | 3/2, 23/16, 11/8, 21/16, 5/4, 19/16, 9/8 |
| 2, 2, 2, 3 | 57 | 19/16, 9/8, 37/32, 9/8, 37/32 |

Both remaining profiles require total measure at least 9/8. Twelve disjoint events in the unit probability space cannot attain this. The upper bound uses K₃,₄. Distinct edges activate at least two of its three row vertices or at least two of its four column vertices. Four and seven formula gates compute the respective threshold-two functions. One final OR, seventeen vertex OR gates, and twelve pairing gates give 41.

The exact rational verifier is arbitrary_formula_volume.py with the shared profile helpers in endpoint_volume.py. The conclusion establishes optimality within the stated endpoint-bank architecture. Shared internal gates in the tail and circuits with other input preprocessing are outside the theorem.
