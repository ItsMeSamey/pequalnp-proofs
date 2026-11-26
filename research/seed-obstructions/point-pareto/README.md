# Exact point-gate costs for boundary widths eleven through fourteen

| Maximum boundary width | Minimum paid point gates | Maximum mixed gates under total budget 33 |
| --- | ---: | ---: |
| 11 | 9 | 24 |
| 12 | 5 | 28 |
| 13 | 0 | 33 |
| 14 | 0 | 33 |

The minimum is taken over point banks that separate every point obligation below. Each matching upper bound is attained by binary OR gates. The two nonzero lower bounds apply to the point component of every full residual separator with the indicated boundary width.

Each point-side wire has a thirteen-bit mask giving its values on singleton point inputs. On these masks, the two gate types act by union and intersection. The starts consist of thirteen singleton masks and the eighteen already computed point-side masks from the six frozen groups. For each group the two pair masks and their four-point union are free.

For each sample pair consisting of a positive row and a negative row whose line portion dominates the positive line portion, some point-side boundary wire must distinguish the pair. The positive point portion is a singleton p. If the wire's singleton mask met the negative point input n, monotonicity would force the wire true on n. Thus a necessary condition is a boundary mask containing p and disjoint from n. Keeping just the largest negative point sets for each p gives 1,323 obligations from the pinned residual statement.

An eleven-wire bank with at most eight paid gates would have at most eight selected nonraw masks. The exhaustive and structural arguments below exclude every possible number of selected masks.

## Exact encoding

Give every distinct computed mask an index according to its unsigned numerical value. A shortest program on the singleton domain has distinct, nonraw, nonzero results. Repeated or raw results can use the earlier wire. An empty result can be propagated as a constant and removed by simplifying its downstream unions and intersections, and it cannot discharge a separation obligation. A shorter program can be padded to the requested length by appending unused, distinct two-raw unions. There are 327 available nontrivial two-raw results. These operations justify the exact gate count in the ranges checked here.

Each computed mask chooses an expression. For two raw operands the checker lists the distinct resulting masks. For one raw and one computed operand it enforces the appropriate bitwise truth table. For two computed operands the checker enforces the same truth table on both computed values. With distinct masks, a union result is strictly larger than either computed operand and an intersection is strictly smaller. This identifies the operation from the sorted indices. Separate variables for precedence define an acyclic order that respects all chosen expressions. Sorting the masks therefore does not restrict the chronological order of gates. A width constraint applies to selected boundary wires. Intermediates may be omitted from the boundary.

## Reproduction

Run `./verify.sh` in this directory with Python 3 and python-sat (CaDiCaL 1.9.5). The pinned statement is bundled. The four commands below certify the lower bounds. The star-recovery command also reconstructs the upper bounds.

```sh
python six_outputs.py L-meta-18968.json
python check.py L-meta-18968.json --width 11 --gates 8 --selected 7 --single-hidden
python check.py L-meta-18968.json --width 11 --gates 8 --selected 8
python check.py L-meta-18968.json --width 12 --gates 4
python star_recovery.py L-meta-18968.json
```

The three `check.py` invocations return UNSAT. Each supports `--cnf point.cnf --proof point.drat`; `drat-trim point.cnf point.drat` checks its proof independently.

## Six selected nonraw masks

The independent search in `six_outputs.py` first rejects arbitrary banks with at most five selected nonraw masks and eleven selected masks in total. It then enumerates every numerically sorted six-tuple of arbitrary masks which, together with at most five selected raw masks, separates the 1,323 obligations. A blocking clause removes the six-tuple alone, so different choices of raw masks are counted together. There are 15,616 tuples. Each of the six masks has at least two points, is contained in exactly one residual star, and has a different host star from the other five masks. Exactly 6,064 tuples have zero outputs realizable from one raw pair, 7,392 have one, 1,968 have two, and 192 have three.

This branch requires at least nine paid gates. In every tuple at least three outputs have size at least three. Call these large outputs. Every raw mask and every other boundary output has intersection of size at most one with the host star of a given large output. If an OR gate produces a large output, one of its parents contains at least two of its points and is a hidden wire lying inside its host star. Different host stars require different such parents. If an AND gate produces a large output, both parents contain that output and must both be hidden. With only two hidden wires their intersection can yield at most one large output, and neither parent can then lie inside another large output's star. Hence two hidden wires cannot supply three large outputs.

## Seven or eight selected nonraw masks

When seven masks are selected, at most one of the eight gates is hidden. The checker orders the seven boundary masks and gives the hidden gate a separate label. It permits either operation wherever the hidden label prevents the numerical ordering from fixing the operation. It checks acyclicity on all eight gates, including the hidden gate. Any seven-gate implementation with seven selected outputs can receive an unused eighth gate. This case is unsatisfiable. When eight masks are selected, all eight results are boundary masks and can be put in strict numerical order. This case is likewise unsatisfiable. Together with the six-mask argument this proves the nine-gate lower bound.

## Star recovery by OR gates

For comparison, the optimal eleven-wire bank that recovers all seven stars by unions uses nine paid OR gates. Fix the selected singleton raw inputs. For a star missing d points, allow q selected nonsingleton submasks. Gates producing nonsingleton subsets of two different stars cannot be shared because the stars meet in at most one point. On one star at least q gates are needed for its q outputs and at least d−q gates are needed to connect d distinct missing points to q outputs. For a width bound, q never needs to exceed d. These bounds are attained by distributing the missing points among q groups as evenly as possible, padding a one-point group to a pair inside the star. At optimal local cost when extra groups are unnecessary they may simply be omitted. The minimum total at each allowed width follows by a dynamic program over seven stars and all subsets of the thirteen raw singletons. Computing a local output by unions cannot benefit from a nonsingleton raw input, since every such input meets each star in at most one point.

`star_recovery.py` computes the costs 21, 18, 15, 12, 9, 5, 0 at widths seven through thirteen and checks a concrete nine-gate, eleven-wire example on every point obligation.

At width twelve, the unrestricted projection also has exact cost five. Run `check.py --width 12 --gates 4` on the same input for the lower bound, and use the five disjoint two-point ORs in the star-recovery construction for the upper bound. The thirteen raw singleton wires give cost zero at width thirteen or greater. If exactly fourteen distinct boundary wires are requested for this relaxation, the bank can also include any one of the remaining eighteen raw point wires.

## The six-selected case at equality

Exactly 24 eleven-wire banks with six selected nonraw masks attain the nine-gate minimum. To see why the enumeration is small, give each large output its host star. A hidden mask is local if it has size at least two and is contained in a host star. With h local and 3−h nonlocal hidden masks, at most h hosts can use a local mask. Every remaining large output needs an AND of two nonlocal masks. This bounds the number of large outputs by h plus the number of pairs of nonlocal masks. Since there are at least three large outputs, either all three hidden masks are local or all three are nonlocal. In the nonlocal case all three pairwise intersections would be required. The earliest hidden mask would then contain an as-yet uncomputed large output, although each of its two available parents meets that output's star in at most one point. This is impossible. In the local case each of the three large outputs has its own hidden mask. Before that output, every other available mask meets its star in at most one point. Hence its hidden mask is a pair, and the final output is a triple. The remaining three boundary masks are pairs. Conversely these three pairs and three triples cost exactly nine independent OR gates to construct.

The six-output enumeration contains exactly 24 tuples of this shape. The remaining obligations in each case uniquely determine the five raw singleton boundary wires. Reproduce the list with the following commands.

```sh
python six_outputs.py L-meta-18968.json six-tuples.txt
python nine_leaf_banks.py L-meta-18968.json six-tuples.txt
```

## The complete minimum-width-twelve domain

At twelve wires and five paid gates there are exactly five admissible boundary banks. Each selects seven raw singleton wires plus five nonraw outputs, and each computed output can be obtained directly from two raw inputs. The families are listed in `cost-five-width-twelve.txt`. Two contain a three-point signature extending outside every single residual star. Run `python width12_equality.py L-meta-18968.json` to exclude every other five-output tuple and enumerate all raw complements in the five remaining cases.
