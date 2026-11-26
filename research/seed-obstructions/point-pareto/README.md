# Point-gate cost at a boundary of eleven wires

Each point-side wire has a thirteen-bit mask giving its values on singleton point inputs. On these masks, the two gate types act by union and intersection. The starts consist of thirteen singleton masks and the eighteen already computed point-side masks from the six frozen groups. For each group the two pair masks and their four-point union are free.

For each sample pair consisting of a positive row and a negative row whose line portion dominates the positive line portion, some point-side boundary wire must distinguish the pair. The positive point portion is a singleton p. If the wire's singleton mask met the negative point input n, monotonicity would force the wire true on n. Thus a necessary condition is a boundary mask containing p and disjoint from n. Keeping just the largest negative point sets for each p gives 1,323 obligations from the pinned residual statement.

The checker represents a bank by up to eleven selected raw or computed masks. Six binary gates cannot supply such a bank. This gives a lower bound of seven paid point gates under the eleven-wire boundary restriction.

## Exact encoding

Give every distinct computed mask an index according to its unsigned numerical value. A shortest program on the singleton domain has distinct, nonraw, nonzero results. Repeated or raw results can use the earlier wire. An empty result can be propagated as a constant and removed by simplifying its downstream unions and intersections, and it cannot discharge a separation obligation. A shorter program can be padded to the requested length by appending unused, distinct two-raw unions. There are 327 available nontrivial two-raw results. These operations justify the exact gate count in the ranges checked here.

Each computed mask chooses an expression. For two raw operands the checker lists the distinct resulting masks. For one raw and one computed operand it enforces the appropriate bitwise truth table. For two computed operands the checker enforces the same truth table on both computed values. With distinct masks, a union result is strictly larger than either computed operand and an intersection is strictly smaller. This identifies the operation from the sorted indices. Separate variables for precedence define an acyclic order that respects all chosen expressions. Sorting the masks therefore does not restrict the chronological order of gates. A width constraint applies to selected boundary wires. Intermediates may be omitted from the boundary.

Run with Python 3 and python-sat (CaDiCaL 1.9.5).

```sh
python check.py L-meta-18968.json --width 11 --gates 6 --cnf point.cnf --proof point.drat
drat-trim point.cnf point.drat
```

The obstruction concerns the singleton projection, a necessary relaxation of a full residual separator. Feasibility in this projection alone only supplies a point-bank witness.

## Six selected nonraw masks

The independent search in `six_outputs.py` first rejects arbitrary banks with at most five selected nonraw masks and eleven selected masks in total. It then enumerates every numerically sorted six-tuple of arbitrary masks which, together with at most five selected raw masks, separates the 1,323 obligations. A blocking clause removes the six-tuple alone, so different choices of raw masks are counted together. There are 15,616 tuples. Each of the six masks has at least two points, is contained in exactly one residual star, and has a different host star from the other five masks. Exactly 6,064 tuples have zero outputs realizable from one raw pair, 7,392 have one, 1,968 have two, and 192 have three.

This branch requires at least nine paid gates. In every tuple at least three outputs have size at least three. Call these large outputs. Every raw mask and every other boundary output has intersection of size at most one with the host star of a given large output. If an OR gate produces a large output, one of its parents contains at least two of its points and is a hidden wire lying inside its host star. Different host stars require different such parents. If an AND gate produces a large output, both parents contain that output and must both be hidden. With only two hidden wires their intersection can yield at most one large output, and neither parent can then lie inside another large output's star. Hence two hidden wires cannot supply three large outputs.

Seven paid gates with all seven outputs selected are also infeasible. Together these results raise the unrestricted point-cost lower bound at width eleven to eight. Use the following commands to replay the two branches.

```sh
python six_outputs.py L-meta-18968.json
python check.py L-meta-18968.json --width 11 --gates 7 --selected 7
```

## Star recovery by OR gates

For comparison, the optimal eleven-wire bank that recovers all seven stars by unions uses nine paid OR gates. Fix the selected singleton raw inputs. For a star missing d points, allow q selected nonsingleton submasks. Gates producing nonsingleton subsets of two different stars cannot be shared because the stars meet in at most one point. On one star at least q gates are needed for its q outputs and at least d−q gates are needed to connect d distinct missing points to q outputs. For a width bound, q never needs to exceed d. These bounds are attained by distributing the missing points among q groups as evenly as possible, padding a one-point group to a pair inside the star. At optimal local cost when extra groups are unnecessary they may simply be omitted. The minimum total at each allowed width follows by a dynamic program over seven stars and all subsets of the thirteen raw singletons. Computing a local output by unions cannot benefit from a nonsingleton raw input, since every such input meets each star in at most one point.

`star_recovery.py` computes the costs 21, 18, 15, 12, 9, 5, 0 at widths seven through thirteen and checks a concrete nine-gate, eleven-wire example on every point obligation.

At width twelve, the unrestricted projection also has exact cost five. Run `check.py --width 12 --gates 4` on the same input for the lower bound, and use the five disjoint two-point ORs in the star-recovery construction for the upper bound. The thirteen raw singleton wires give cost zero at width thirteen or greater. If exactly fourteen distinct boundary wires are requested for this relaxation, the bank can also include any one of the remaining eighteen raw point wires.
