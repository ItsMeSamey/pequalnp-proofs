# Two arbitrary shared insertions into the 31-gate partial separator

The fixed seed has 31 binary gates. It accepts 25 of 28 positives and rejects all 245 negatives. The data and numeric gate order are copied from the independent residual review. A gate operation of 0 means OR and 1 means AND.

The two added gates may each use any primitive or old gate output, and the second can also use the first. Each of the 62 old input pins may independently keep its original wire, use the first added gate, or use the second. The output may be the old output or either new gate. Sharing either new gate has no limit. Dead wires are permitted. Commutativity orders the inputs of each added gate. Naming its two additions in a topological order covers both possible dependency orientations.

With --unordered, the old gates retain their operation and their retained edges, but may be reordered after rewiring. For each added gate J, a Boolean flag propagates from every old pin redirected to J downstream along all retained old edges. Neither J nor any earlier new gate can take a source flagged for J. This excludes all cycles, because every new cycle must include at least one addition, and a path from the second new gate back to the first is also excluded by the chosen topological naming. Any acyclic instance has a labeling satisfying these implications by marking precisely the reachable old gates.

Run with Python 3 and python-sat.

```sh
python insert.py --unordered --budget 100000
python insert.py --unordered --solver glucose4 --budget 100000 --seed 153
python controls.py
```

CaDiCaL certifies unsatisfiability on 29 sampled rows and Glucose on 32, so no setting of these additions and reroutings matches all 273. The six positive controls pin varied topologies and generate independent expected truth values on all rows. Their success tests the operation and mux encoding. These experiments cover a specific seed and repair class.

The optional --rewires parameter enlarges the search by allowing at most that many old pins to take an arbitrary earlier old or raw source. Timeout on this enlarged class supplies no lower bound.
