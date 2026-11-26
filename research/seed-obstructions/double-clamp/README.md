# Two extra line masks and punctured ordinary branches

This is a read-once mixed tree with P=11 point leaves and nine line leaves. Seven are raw singleton line bits and the others are masks S,R of size ≥2. Replace the latter by disjunctions of their raw inputs. The original point and line precomputation plus the nineteen tree gates must exceed 33 in all 531 banks below.

Pin both extras to one. The punctures are those point singletons p where no negative containing p has both masks active. Away from the punctures the pinned tree rejects every zero-raw-line point singleton and accepts the incident positives. In the 531 banks, every pair of distinct ordinary lines L,K has a pinned negative containing a point on each outside the punctures. At a split, the two positive tests would force an AND's opposite children true at these points with zero raw lines, contradicting rejection on their union. Rejection propagates through OR and through AND attachments whose guards cover the resident point. Thus every raw-line split is OR. The following also gives conditional results for the no-split-AND topology when some raw pairs lack this witness.

When discarding point-only OR attachments, recover ordinary neighborhoods using private AND guards, possibly retaining clamped special blocks. An incident point p of T is guaranteed pivotal at T's true flag pattern if any negative contains p with all T's flag bits on: with those flags at zero raw lines the root must reject p. At a pivot every AND sibling on T's path is active. Let G_T be these guaranteed pivotal points, which include all incident points outside the punctures. After deriving an expression accepting G_T and rejecting exterior singletons, OR in the omitted target points at one gate each. The seven singleton signatures alone require 21 point gates by ../../seven-neighborhoods/README.md.

A special block is a maximal subtree with no ordinary line leaf, containing at least one extra line mask. The two extras share a block or occur in disjoint blocks. A block at an OR attachment may be discarded since the pivotal tests do not need it. Otherwise it is an AND side attached to a resident set A of ordinary leaves. For disjoint blocks their resident sets A,B are laminar, possibly equal. Empty sets represent removal. For t in a block's resident set its cofactor at t's flags accepts G_v for every other resident v whose flags on the block are a subset of t's flags. On a t-active negative the actual block dominates that cofactor. Thus retain the cofactor or drop it if a suitable other resident supplies a witness.

For the ordinary shared guards on t's path use a line u from the sibling branch of its nearest ordinary binary ancestor. G_u activates every shared guard. Candidate u lie in the smallest nontrivial set A or B containing t, when present. For each exterior singleton x the checker seeks a sampled t-active negative containing x, meeting G_u, and meeting the union of G_v for each dropped special block that matters to t. This forces the shortened private conjunction to reject x. The checker requires this for all candidate u, overapproximating the possible sibling branches.

## Counting point gates

Each block may be retained by one output in the basic accounting. Building its cofactor costs one fewer gate than its nonconstant point leaf count, and adds one input occurrence. Seven nonconstant outputs therefore cost at most P−7 plus repairs. A direct target uses three raw ORs; omitting its expression from that count gives a penalty four. If for every candidate u at least one negative forces all nonprivate guards true when t is active, some purely point-side private AND attachment is necessary, and its unused leaf lowers the direct penalty to three. Distinct direct targets have disjoint private leaves. Dynamic programming assigns retained blocks, direct outputs and repairs. The affordable penalty is c+2, where c is the line-gate lower bound: 21−(P−7+penalty)+19+c≥34.

If a joint block has e point leaves, it can instead serve two targets. For e≤4 the two cofactor prunings together cost at most e gates by ../one-surplus/prune4.py. They introduce two input occurrences, for penalty two plus their two repair counts. For e≥5 ignore the block and build both targets directly. Relative to P−7 the penalty is at most 8−e≤3 (all e occurrences unused, neither target needs repairs). Thus use the maximum of three and two plus their repair counts. No other target uses the joint block in this alternative.

For a joint AND block J with residents A, a negative n forces J to one if some T in A has its flags active and n meets G_T. This follows from the positive singleton pivot on T. If every point p belongs to some such negative, the outer context with raw lines zero and J pinned one rejects p, by monotonicity. The both-extra-pinned formula at p is bounded by this context. Apply the full-good theorem in ../ordinary-line-nine/README.md for that placement.

## Replay

Run in this directory using Python 3 and C++17. The sample decoder and raw JSON are in ../one-surplus.

    python allbanks.py
    python prep.py
    python prep_single.py
    python jointall.py
    g++ -std=c++17 -O3 certfinal.cpp -o certfinal
    ./certfinal <singlebanks >checked-singlebanks
    awk '{n[$5]++} END {for (i in n) print i,n[i]}' checked-singlebanks

The verifier checks line costs at most five as P=11 costs nine point gates. Intersecting S,R need at least |S union R|−1 line gates and disjoint ones at least |S|+|R|−2. The 531 banks lack global both-extra pinning but possess all ordinary-split pair witnesses. All 531 pass. An optional run on allsingle gives conditional results for other no-AND placements. Full-good banks and exceptional AND placements have separate proofs.
