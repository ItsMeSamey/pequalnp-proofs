# The ordinary threshold-two minimum determines the crown minimum

Let C(n) be the minimum size of a monotone binary AND/OR circuit for ordinary threshold two. Let G(n) be the minimum size of a monotone binary circuit for the n-by-n crown on the promise of one selected row and one selected column, with unrestricted fanout. For every n≥2,

    G(n) = n + C(n).

In particular, the sharp third-order coefficient and the established remainder bounds for C(n) transfer verbatim after replacing its leading 2n by 3n. The finite conclusion for n=13 is G(13) in {44,45} until the remaining threshold case is settled.

## Costs and observers

Pairing each row raw with its corresponding column raw by an OR proves G(n)≤n+C(n). The prefix construction for threshold two uses at most 3n−5 gates for n≥2. Write G=G(n) and v=G−2n+1, so v≤2n−4. Every raw is used in a live minimum: an unread row would be componentwise dominated by every other row, contrary to the two differing entries; the column argument is identical. Constants and one-input gates can be simplified. Use the reverse-direction network, its physical union accounting and transposition from `universal-pairing.md` and `direct-coordinate-restriction.md`. It has at most v paid binary unions, a full source, signed switch branches, and one raw observer for each row or column. A label i has a direction where both its observers are false and all others true. Opposite-shore observers at different labels have full union.

For comparable row/column twins use the larger observer for both. Full opposite-shore unions and rejecting representatives persist. Equal observers use the same physical output. All raw masks left at different labels are incomparable by their representatives. An observer equal to a signed branch is read there directly; every remaining distinct mask needs a paid union. When at most two labels have incomparable twins, observe one mask per label: use opposite shores at the two exceptional twins if there are two. The chosen masks have pairwise full union, and each is false at its own representative. Transposition gives an n-input threshold-two circuit of size at most v+n−1=G−n.

## Removing and restoring labels

Suppose n≥4 and d≥3 labels have incomparable twins. Delete k=max(2,d−2) such labels. Then 2≤m=n−k and at most two incomparable labels remain. The deleted labels had 2k distinct masks, of which s are direct. Replace each nondirect deleted observer by the full source everywhere it was used, removing 2k−s distinct binary unions. All modified values agree with their old values on every retained representative (the replaced masks were already true there). Other masks can only grow, preserving full opposite-shore unions. Existing physically paired labels remain paired.

Restrict each of the s direct branches to its chosen coordinate sign. When s>0 these are distinct coordinates with a common retained representative, and the incoming activations at the corresponding switches are nonempty on that face. We recall why a retained receiver M suitable for the coordinate-restriction lemma exists. If all designated direct branches are on one shore, any opposite-shore observer from a retained label suffices. If direct observers occur on both shores, two opposite-shore direct branches at different labels cannot cover the cube on different axes. Opposite signs on one axis cannot both contain the representative of a third label; equal signs cannot cover the cube. Thus in the mixed-shore case all direct observers belong to one label and there are at most two in the original network. The n+d distinct original masks would require at least n+d−2 paid unions, so d≤v+2−n≤n−2. There is an originally paired label among the retained ones; take its paired observer M. In both cases M is nonempty and nonfull on the face by two retained representatives, and has full union with each designated mask. The full union is preserved through the preceding replacements.

The finite-forest lemma `direct-coordinate-restriction.md` removes at least s additional binary unions. For s=0 no second step is needed. The remaining at most v−2k unions give, by choosing opposite shores at the at most two remaining incomparable twins and transposing, a threshold circuit on m labels of size at most v−2k+m−1. If this union budget is negative the configuration was impossible. Split an input z into z₁∨z₂ and OR the output with z₁∧z₂. This adds three gates and implements threshold two on one further input. After k such splits the size on n inputs is at most

    v−2k+m−1+3k = v+n−1 = G−n.

This last lifting step proves the required inequality directly; it does not require a pre-existing lower bound on a smaller threshold minimum.

For n=3 we have v≤2. Three incomparable twins would require six distinct observer masks. There are at most three direct observers if they all lie on one shore and at most two in the mixed-shore case by the third-representative argument. The two paid unions cannot supply the remainder. Thus at most two exceptional twins occur, handled above. For n=2 every one of the four raw inputs is essential; a binary circuit of size at most two has at most three distinct inputs in its live cone. The usual two cross-ANDs and one OR achieve size three, which equals 2+C(2).
