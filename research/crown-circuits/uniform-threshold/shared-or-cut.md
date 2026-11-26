# A shared-group lower bound for monotone threshold two

For n≥4, C(n)≥2n+(√(8n−7)−7)/2. By the regular-or-delete lemma in threshold-lower.md, either C(n)≥C(n−1)+3 or a globally minimum circuit has precisely two distinct OR readers at each raw. Take such a regular circuit of size g=2n+s. Flatten single-use OR-to-OR trees. Raw labels are edges of a simple graph on the OR groups: internal repetition is redundant and two labels in both the same groups are indistinguishable when adding one to the other's singleton. A raw-bearing group cannot be the output, so a singly used raw-bearing group feeds an AND. Let H be the set of all shared OR groups including zero-raw groups, h=|H|, and f be physical fanout with pins counted separately. The sum of f−1 over nonoutput internal gates is 2g−2n−(g−1)=s+1, hence h≤s+1.

## Four edges avoid shared groups

If x's two singly used groups had the same AND reader, factor x out of (x∨P)∧(x∨Q), removing its occurrences from both private OR trees and adding one OR. This saving contradicts minimum size. Thus each edge avoiding H prescribes a pin at each of two distinct ANDs. Two such edges must have conflicting pin choices, since otherwise selecting both leaves every signal outside their two to four selected OR groups zero by topological induction: a direct reader of a selected group is an AND and none has both pins among the selected groups. No other group has a true raw. The quarter subcubes in the space of simultaneous AND pin choices are therefore disjoint and at most four edges avoid H.

## Flow at a shared group

For U∈H set all raws zero and override U's output to true. Call true wires active. Let L_U count active edges into inactive ANDs. Every active OR group other than U has at least one active nonraw input, every active AND has two active inputs. Subtract internal active edges from total active outflow to obtain

    L_U ≤ f_U + Σ_(active W∈H other than U)(f_W−1) + Σ_(active AND A) max(f_A−2,0).

Singly used active intermediate ORs contribute at most zero and output fanout zero causes no positive error. Active W≠U lies downstream of U. It cannot share a raw x with U: x=true forces U and thus by monotonicity forces the same nonraw operand that was true in W at the probe. Dropping x's redundant occurrence from W would save a gate. The ordered active shared pairs (U,W) thus charge distinct missing unordered shared edges, by acyclicity.

## Star and its boundary

If U has degree k≥3, retain its k incident raw labels and override U to true. This computes threshold two on the star since U was already true on every nonempty assignment, and empty rejects by monotonicity. Each singly used neighbor V is x∨Q_x for its sole incident star variable. Q_x is independent of x since x's only other occurrence was in the overridden U. Q_x rejects every other singleton y, or y and y+x are indistinguishable. Independence and monotonicity imply Q_x rejects x and empty as well, hence Q_x implies threshold.

Simultaneously bypass each selected V to x and adjoin the resulting Q'_x to the output as terminal disjuncts. Internal values only decrease so Q'_x≤Q_x remains clean. For a lost positive take the earliest changed V: x is zero, and its unchanged nonraw operands still make Q'_x true. This restores the positive. All internal values at empty remain unchanged. Keep the unsimplified graph. Each x now has precisely its original AND reader: all new terminal disjuncts use nonraw predecessors of the selected groups; no such predecessor can itself be a selected V_x, which has only an AND reader. Nor can any singleton-clean Q'_y equal raw x.

If the AND partner of x is false at empty, it remains false on singleton x by independence, so all downstream values equal their empty values. Two such x,y with different AND readers are impossible: y's partner still vanishes on singleton x and adding y cannot change the output. If x,y have the same reader x∧y, the third singleton z is indistinguishable from x+z. Thus all but at most one singly used neighbor have a true partner at star empty, exactly the original probe. Their own V pins are false, giving distinct active-to-inactive AND pin edges. Neighbor pairs sharing a reader have two false pins and cannot be charged. The number of singly used neighbors is at most 1+L_U. When k≤2 use the direct degree bound 2≤1+f_U instead.

## Summation

Write m for the number of shared–shared edges, δ_O=Σ_H(f_W−2), and δ_A=Σ_nonoutputAND(f_A−1). Then δ_O+δ_A=s+1−h. The bases 1+f_U sum to 3h+δ_O. The active shared unit contributions globally sum to at most binom(h,2)−m. Each extra f_W−2 occurs at most h−1 times and AND contributions are at most hδ_A. Adding the three edge classes gives, for h≥1,

    n ≤ 4 + m + 3h + δ_O + binom(h,2)−m + (h−1)δ_O + hδ_A
      = 4 + 3h + binom(h,2) + h(s+1−h).

For h=0 already n≤4. The right side increases through h≤s+1 to (s²+7s+14)/2. Since s≥−1 the rearrangement gives s≥(√(8n−7)−7)/2. Base C(4)=7 suffices and for n≥5 the square-root correction increases by at most one at the next input, so the three-gate deletion alternative preserves the bound. This yields second-order coefficient √2.
