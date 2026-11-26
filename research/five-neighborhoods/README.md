# Five projective neighborhoods require fifteen binary set gates

## Statement

For i=0 through 6 let T_i={i,i+1,i+3,i+9} modulo 13. Choose any five of these seven lines, and restrict the underlying point universe to their union. Every point mask meeting each chosen line in at most one point is free. A paid gate takes the union or intersection of two earlier masks, with arbitrary reuse. The exact minimum number of paid gates needed to make the five full masks available is 15. The same minimum for one, two, three or four selected lines is three times their number.

This is a singleton-signature theorem. Original residual lines 6 through 12 become lines 0 through 6 by a simultaneous cyclic shift of points and lines. The 13 raw points and all 18 supplied point-OR features are free in the relaxation because each external prefix line meets each retained line in exactly one point. Separate four-point unions attain the upper bound using raw points alone.

## Marked projections

An output is marked if it is computed by an intersection, or by the union of a singleton with an intersection that accepts exactly three points of that target and no other points. A marker is a paid gate even if projection gives it equal operands. When projecting a circuit onto a subfamily, replace any mask that now meets every retained line in at most one point by a free input. All marked intersections still meet their own line in at least three points. They and their marked roots can therefore be retained, even if other gates cease to be needed.

The exact marked minima for one, two and three full targets are 4, 8 and 12. An ordinary three-gate union followed by an identity intersection gives four per target. For the one-target lower bound, prune every intersection to one operand. The resulting union cone still covers four points and has at least three unions since each free mask covers at most one. The mark adds an intersection. The included SAT verifier excludes seven gates for a pair and eleven for a triple. Every shorter marked circuit can be padded by appending identity intersections to its last output. All pairs are equivalent. Two incidence types suffice for triples, the triangle and the concurrent triple.

The verifier sets one Boolean variable for each gate and point. Each port selects an earlier signal or an independently chosen free mask. Pairwise clauses forbid a free port from containing two points of any target. Operation clauses implement coordinatewise union or intersection. A designated output has exactly the target mask. An OR-root explicitly selects a free operand and a three-point AND operand; the target mask forces the free operand to supply the fourth point. The first three slots cannot be marked outputs by the one-target lower bound.

A minimal circuit can omit any paid transversal and any dead gate. Markers remain because they are nontransversal. The verifier permits repeated parents, equal mask values, and fanout. Order the two source indices of each gate, with any free mask represented by index -1. A topological gate order nondecreasing in the pair (larger source index, smaller source index) exists: among available gates select the least pair; every newly available gate has just acquired a later source. Initially available gates with two free sources can be sorted lexicographically by output bits. The CNF uses these two symmetry reductions. Finally, a subfamily of one or two marked targets needs the already proved minimum number of gates having a nonsingleton intersection with at least one retained line, since all other gate masks become free there. The verifier adds these cardinality constraints. It checks the seven-line incidence geometry and the coverage of the finite pair/triple types.

## Reduction from a deficient family to marked outputs

Suppose k is the least size of a subfamily realizable in fewer than 3k gates. Use a minimum circuit, with no dead gates, duplicate mask values, or paid free masks. A target whose cone uses only unions costs at least three paid gates. All masks in that cone are contained in that target and become free after deleting it. Such a target would leave a smaller deficient family. Thus every target cone includes an intersection.

For a target T, call a paid mask exclusive if it meets T in at least two points and every other retained line in at most one. At most two paid masks are exclusive to T, or deleting T removes at least three gates. The output itself is exclusive. Follow a path from a last intersection in its cone through only unions to the output. That intersection gives a mask inside T. It has at least two points since otherwise it would be free. If the output is a union, this intersection and the root already use both exclusive masks. A union root has both operands inside T, so all operands other than that intersection have at most one point. Duplicate operands would be redundant. Thus the intersection has three points, and the other operand is the fourth singleton. If the output is itself an intersection, it is directly marked. Every target in a least deficient family is therefore marked.

One target needs three ordinary gates by the union-pruning argument. The marked pair and triple bounds exclude k=2 and k=3. For k=4, keeping any three marked outputs costs twelve by the marked triple bound and removes at least the fourth output. This excludes k=4 as well.

## Excluding k=5

Suppose five lines use at most fourteen gates. Keep any three lines and delete the other two. The two deleted outputs become free masks on the retained lines, whose marked circuit costs twelve. The full circuit therefore has exactly fourteen gates. No third gate can be lost in any such projection.

1. Every target output must be an intersection. An OR-root would also lose its separate three-point intersection when that line is deleted.
2. Each of the nine nonoutput gates meets at least three lines in at least two points, since otherwise choosing its two potentially rich lines for deletion would make it free.
3. The last nonoutput gate directly feeds at least three target outputs. Otherwise remove its output consumers among the two discarded lines and it becomes dead. Every later gate is an output.

Make a graph on the distinct parent masks of the five intersection outputs, labeling its edges by their intersection lines. It is simple. At an edge with both endpoints of degree at least two, any other incident edges on opposite ends have their line intersection on the middle edge. Consequently all the line labels at both ends belong to a single pencil: fixing one neighbor at each end fixes its intersection with the middle line, hence fixes the common point for every neighbor. This pencil propagates over adjacent internal edges since two distinct lines determine their common point. Every component is therefore a star or has all its labels concurrent. No four of the seven selected lines are concurrent, as checked directly.

The last nonoutput gate has degree at least three. Its component is consequently a star (a three-edge pencil with degree three is itself a star). Let its size be s. A leaf parent intersects the center precisely in its label, so it meets every other star line at just that line's intersection with its own label. As a nonoutput gate it must meet at least three lines in at least two points. Hence 1+(5−s)≥3 and s=3. This three-edge component needs four parents, and the two remaining edges need at least three more. The full circuit has at least seven distinct parent masks, each containing an entire target.

At most two gates besides those parents and the five outputs remain. The first two gates g1,g2 cannot already contain an entire line: two unions span at most three points there and intersections cannot increase coverage. Hence they are precisely the two remaining gates, and each is a union because an intersection with a free operand would still be free. Every later signal contains at least one entire target.

Inductively every full-bearing signal contains g1. An intersection containing a full target must take two full-bearing inputs. A union with a full-bearing input inherits g1. A union with no full-bearing input has available only free masks and g1,g2. If g2 depends on g1 then g2 contains it. Otherwise g2 is a union of two free masks and cannot span four points together with one other free mask. Thus the union must contain g1 in either case. This forces g1 inside each target output, contrary to its meeting at least three lines in two or more points. Five targets require at least fifteen gates.

## Reproduction

Python 3 and the single dependency pinned in requirements.txt suffice. Run:

```sh
python -m pip install -r requirements.txt
python verify.py
```

verification.log records the completed run and DIMACS hashes. To save the three DIMACS formulas for another solver, use `python verify.py --export cnf`. A second PySAT backend can be selected with `--solver`. The number of conflicts is solver-specific. The calculation needs no repository files, network data or Lean installation once the Python dependency is installed.
