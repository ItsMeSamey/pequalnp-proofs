# Full-cube edge function L-meta-9822

**The minimum is exactly 18 physical AND, OR and NOT gates** for the posted graph function on all 1,024 inputs, with unrestricted fanout. An explicit 18-gate circuit gives the upper bound. At size at most 17, the signed binary lower bound allows at most one NOT. The one-NOT proof covers shared uses of the inverted signal’s source. Every monotone circuit needs at least eleven OR gates, leaving at most six AND gates, and the finite certificates exclude those cases.

Two independent teams reviewed the complete argument for the posted model. The 207-entry archive includes the aggregate proof, upper circuit, one-NOT case manifest, theta enumeration, and earlier five-AND, six-AND and signed-circuit certificates in their original layouts. Its SHA-256 is `ff40bb6745f18046f74a51ec102e9edbc1e0657dbf95c37bb21b87bc0a7e2493`. The second reviewer verified all 206 listed payload hashes. Both reviews use earlier finite certificates and small-face lower bounds. The official single-file Lean theorem is still in progress. [Download the proof and certificates](exact-9822-research.zip) · [Read the deduction](exact-eighteen.md) · [Posted proposition](posted-gap-public.json)

## Earlier research checkpoints

The minimum unrestricted AND/OR/NOT circuit size is either 17 or 18. Independent source and finite-ledger reviews establish the lower bound of 17 for the full ten-input Boolean cube. The offered problem asks whether every circuit needs at least 18 gates. [Complete 39-file lower-bound and construction replay](signed16-cert/README.md)

The lower bound combines two results. A signed realization with free inversion still needs at least 16 binary gates. Thus any physical circuit of total size at most 16 would be monotone. The independently checked monotone size lower bound is 17. The signed proof uses the first binary gate, a fanout count, the three-shared-gate lower bound, and the exhaustive exclusion of the three- and four-shared-gate cases. Independent full-cube checks covered 249 and 84 cases respectively. This composition has mathematical and computational review. The partial Lean replay below covers the earlier 15-binary deduction. [Three shared gates](physical/third-fork.md) · [Three-gate exclusion](reductions/three-shared.md) · [Four-gate exclusion](reductions/four-shared.md) · [Monotone size bound](monotone-seventeen.md)

At total size 17, the remaining possibilities are a monotone circuit with exactly seven ANDs, or a circuit with one NOT and 16 binary gates. The offered lower bound of 18 remains open.

The 18-gate circuit uses the original ten inputs numbered 0 through 9. Each row defines the next wire from two earlier wires. The independent checker evaluates all 1,024 input assignments.

Identifying inputs 0 and 3 and relabeling the remaining inputs gives the nine-input function in L-meta-11026. Applying the same substitution to the input wires of any circuit preserves its gate count, including every NOT gate. The published lower bound of 16 for the nine-input function therefore applies here. The checker verifies the complete edge image. [Published Lean theorem](https://github.com/open-goat/pequalnp-proofs/blob/aecf602ea3c8da01533a13d2ca03b633689f3033/lean/PEqualNP/Outside/L_meta_11026.lean)

Run `python3 verify.py` from this directory to check both calculations.

For monotone circuits, a size-17 candidate must contain at least two distinct internal AND gates that each accept a nonedge pair. The two pairs can differ. [Rank-two flattening](nonedge-products/rank-two-flattening.md) · [Single exceptional product that accepts a singleton](nonedge-products/sole-hot.md) · [Single exceptional product that rejects singletons](nonedge-products/sole-cold.md)

For unrestricted circuits with at most 17 gates, at least ten gates must be OR or NOT, leaving at most seven AND gates. The proof excludes every possibility with exactly nine OR/NOT gates under the independent binary-gate floor. This earlier argument alone left sizes 16 and 17 open. [Four-inversion exclusion and dependencies](nonedge-products/four-inversions-paid.md)

Every circuit requires at least ten OR or NOT gates even when the number of AND gates is unrestricted. It also requires at least fifteen binary gates even if inversion is free. The earlier 15-binary bound allowed two NOT gates at size 17. The 16-binary bound above reduces that allowance to one. The monotone minimum lies between 17 and 18. Before the 16-binary bound, these facts restricted size 16 to one NOT gate. The fifteen-binary-gate deduction uses the checked signed face of L-meta-9825. [Ten OR or NOT gates](nonedge-products/unrestricted-ten-paid.md) · [Fifteen binary gates](physical/binary-fifteen.md) · [Monotone lower bound](monotone-seventeen.md)

The monotone proof first bounds the number of AND gates by six. The receiver argument covers four or fewer AND gates. Separate enumerations cover five AND gates and six AND gates at a total cost of at most sixteen. Both archives include native code, replay instructions and the enumerated outcomes. [Receiver argument](directions.md) · [Five-AND archive](five-and/five-SHA256SUMS) · [Six-AND archive](six-and-cap16/six16-SHA256SUMS)

Any monotone 17-gate realization must use exactly seven AND gates. The six-AND case was eliminated by an exhaustive native computation covering 41,719 profiles. Independent review checked the search programs, the profile coverage and the archived results. For a 16-gate realization with one NOT, the function feeding the NOT must have minimal positive supports with empty intersection. [Six-AND search and replay](six17-cert/README.md) · [Single-NOT support restriction](nonedge-products/cap16-compulsory.md) · [Ninth-vertex cofactor](verification/h9.md)

In the remaining seven-AND monotone case, a 17-gate realization requires at least four nonfull conditional activations in the reverse search. The three-activation search checked 17,492 representatives at each of three direct-receiver counts. The archive includes the profile accounting, replay programs and positive controls. [One and two activations](seven-two-cert/scope.md) · [Three-activation archive](seven-three-full-cert/)

The signed binary lower-bound deduction now has a Lean replay from the precise prior face hypothesis. The trial checked the deduction and its helper modules. Completing an end-to-end replay of the supplied wrapper requires the published numerical face certificate. [Lean replay scope](physical/signed-floor-replay.md)

Every possible 17-gate realization must share a binary gate output. In the monotone formula model the exact minimum is 18, as established by a 14,603-state protocol calculation. The separate one-NOT argument also excludes size 17 without a shared binary producer. [Monotone formula proof and controls](formula/tight-monotone-formula.md) · [One-NOT formula exclusion](formula/one-not-formula.md)

For four, five or six nonfull conditional activations, 25,563 further profile checks exclude the case in which at most one distinct activation is nonprimitive. The remaining monotone profiles have at least two distinct nonprimitive activations. [Source, controls and ledgers](seven-high-one-cert/)

In the one-NOT case at size 17 the outer cone needs at least seven AND gates. The full circuit has at most seven ANDs by the OR/NOT lower bound, so it has exactly seven. The finite exclusion of six outer ANDs covers the three possible direct-receiver counts. The package contains native source, coverage ledgers and positive controls. [One-NOT finite proof and replay](one-not-six-cert/)

All 140,857 profiles with four to six conditional switches and exactly two distinct nonprimitive activations have also been excluded at each of the three direct-receiver counts (422,571 profile/quota checks). The remaining monotone sector therefore needs at least three distinct nonprimitive activations. The independent audit reconciled the full ledgers and reviewed the final kernels. [Four-switch archive](seven-c4-two-cert/) · [Five- and six-switch archive](seven-high-two-live/)

A monotone size-17 circuit would need at least two distinct shared internal binary gates. The one-shared-gate analysis covers all costs for its shared helper. The one-NOT branch continues to require at least one shared binary gate. [Global case split and antecedents](monotone-one-share/GLOBAL.md)

In the remaining one-NOT case, the inverter cannot take its input from a fully private prefix computing the OR of two raw inputs. The proof covers all ten surviving high-input pairs. More generally a nonraw guard must reject each of the five low singletons. [Ten-pair case split](nonedge-products/private-seven-crosswalk.md) · [Low-singleton exclusion](nonedge-products/low-hot-inverter.md)

At size 17, a circuit with one NOT whose operand is a noninput gate must accept at least one of the five high singletons at that operand. The proof excludes guards rejecting every singleton, including guards with higher-degree minimal inputs. A separate restriction excludes the five low singletons. The unrestricted optimum remains 17 or 18. [Cold guard proof](two-inversions/cold-selector-cut.md) · [Odd-cycle lemma](two-inversions/singleton-cold-odd-cycle.md)
