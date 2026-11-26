# A 30-gate unconditional raw lower bound and a compulsory front wire

The six-point, seven-line restriction needs at least **22 binary AND/OR gates**. The seven separately charged point-source deletions give at least **29 gates** on the normalized residual. Exact front transfer gives at least **30 gates** on the unrestricted raw suffix of L-meta-18968. A raw suffix that omits w54 needs at least **35 gates**: it must lose at least 13 gates on the same restriction. Consequently every proposed 34-gate witness must use w54. The existence of such a witness remains open.

The seven deletions, the transfer adding one gate, and the charge of thirteen without w54 are proved in the point-deletion-core and front-free branch notes. Briefly, raw points 0, 2, 3, 4, 5, 6 are each individually required. The pair consisting of raw point 1 and the free OR of points 0 and 1 is required independently. All vanish on positives at points 7 through 12. After setting these raw coordinates to zero and lowering the remaining point features on negatives, every free point feature is a singleton or zero. Without w54, all six front lines are additionally required by private raw pairs. Removing source vertices from a connected output cone and simplifying zeros saves at least their total operand occurrences. This leaves the same six-point restriction.

## Base computations

Index its six points by 0 through 5 and its seven lines by 6 through 12. The 18 positives have one point and incident line, and there are 33 maximal negatives. The coordinate symmetry group verified in run.py has order 24. One representative point deletion leaves a 12-input core requiring at least 19 gates. The two line-deletion orbits, represented by indices 6 and 7, each also require at least 19 gates. The representatives have 16 positives and 23 negatives, and 15 positives and 29 negatives, respectively. Thus deleting any one of the 13 inputs leaves a core requiring at least 19 gates.

There are two further families of zero restrictions, represented by the triples {0,6,7} and {0,6,10}. Their 24 images each leave ten inputs, twelve positives and sixteen maximal negatives, and both representative computations rule out 15 gates. Each deleted input in these triples has a neighbor outside its triple. All label matrices and neighborhood assertions are generated from the raw statement.

The base search enumerates every supported circuit within its budget, using the recipe order, signal and recipe dominance, symmetry stabilizers, and zero- or one-retention tree constraints explained in point-deletion-core. In every case the unique admissible support contains all retained variables.

## Reductions for the 21-gate search

Choose a smallest circuit and the lexicographically smallest ordinary gate recipe sequence among such circuits. Since each single-variable restriction needs 19 gates, setting any input x to zero can eliminate at most two gates in a witness of size at most 21.

* An input can appear at most twice. If it appears twice, both uses must be OR. An AND use would vanish to zero, also deleting a consumer in addition to the two uses. That consumer cannot itself be a second use of x: a gate combining x with x AND y equals one of its operands. The AND cannot be the output because some required positives have x false.
* A raw input used by AND is therefore unique-use. That AND has exactly one consumer, an OR. Multiple consumers would save at least three gates on deleting x, and an AND consumer would vanish in turn and simplify a third gate before the nonconstant output.
* A wire false at every negative can feed only OR, as its AND with another operand is dominated by the wire itself. It can feed at most one OR: delete it from every OR use and add it once at the output. Negative results are preserved; lost positives are covered by this wire. Two or more uses would save a gate. The dual statement holds for a wire true on every positive.

For a triple E call a source expensive if it is reused, or if it has a unique AND use. Let t be the total fanout of the three sources. Setting all three to zero removes at least t gates, with one extra removed gate for every unique AND use whose other operand is not killed. This can be counted directly. Start a zero propagation token on every one of the t outgoing operand edges. At an affected gate consume the tokens on its inputs. If the gate becomes zero, emit one token on each of its outgoing edges. A gate reduces the number of outstanding tokens by at most one, including when both inputs become zero. A zero AND with exactly one killed input reduces it by at most zero. Every killed gate has at least one consumer, since the restricted output remains nonconstant. When propagation finishes all initial tokens have been consumed, yielding the stated bound.

For each x in E with a unique AND use, choose a surviving neighbor z outside E. The other operand of that AND is independent of x and must be true on z alone. Indeed, on the positive edge (x,z) the output must respond to x, since the singleton z is below a negative. No other wire can deliver x. With only z true, the other operand has the same value as on that edge, hence is true. It stays nonzero when E is erased. Thus if all three sources in E were expensive, at least six gates would disappear. The remaining 16-gate lower bound would contradict a 21-gate budget. The solver rejects exactly this source-class combination on the 24 verified triples.

The core search also checks all thirteen single-variable restrictions at every candidate gate. On each cofactor it greedily replaces a gate by zero when it is false on every positive, by one when true on every negative, or by an earlier signal whose value is at least the proposed value on positives and at most that value on negatives. Later gates in the cofactor are evaluated on these replacements. These rewrites preserve separation by monotonicity and save one gate each. If more than two are removed, the remaining 19-gate requirement is impossible. If c live wires in the original search frontier have become constants in the cofactor, at least c further gates can be eliminated from the remaining suffix. To see this, treat the frontier as distinct sources of the connected remaining cone. Remove those c sources, keeping the remaining directed paths to the output. In the underlying multigraph the cycle rank falls by total removed-source fanout minus c. Constant propagation is achievable by edge deletions and contractions, and introduces no new sources. The nonconstant result therefore saves at least total removed-source fanout, hence at least c gates. This works for fixed zero and fixed one and counts only gates in the remaining suffix.

The sole 13-input support exhausts without a 21-gate completion.

## Reproduction

From this folder run the following with Python 3.10+ and an AVX2-capable x86-64 compiler. The last path holds the pinned raw L-meta-18968.json and verify_packing.py decoder.

```sh
g++ -std=c++20 -O3 -march=native base.cpp -o /tmp/l-meta-cofactor-base
g++ -std=c++20 -O3 -march=native verify.cpp -o /tmp/l-meta-six
python3 run.py /tmp/l-meta-cofactor-base /tmp/l-meta-six ../seed-obstructions
```

## Verification scope

An independent native replay returned UNSAT on all six searches in the [result table](native-replay.log). Comparing each native input with the driver output from the pinned theorem showed identical positive rows, maximal negative rows and mandatory supports. The four symmetry-enabled inputs also agreed on the full permutation group. The independent triple-deletion searches used the weaker baseline without symmetry pruning.

Separate proof and code review checked the cofactor and retention charges, the additional charge for live constants, both triple orbits and the surviving-neighbor condition. It independently reconstructed the 24 forbidden mask triples and confirmed the 5,760 qualifying entries of the 8,192-entry quota table. These are finite search and paper results.

The six-point core optimum is 22 or 23. For the upper bound, OR the three line neighbors of each point, AND that result with the point, and OR the six resulting terms. The driver checks this 23-gate circuit on all 51 rows.
