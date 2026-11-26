# Independent ten-receiver packing check

This checks the helper-library test on complete six-axis profiles from the portable threshold-ten replay. The file canonical.txt comes from the profile enumerator. This kernel does not use the chronological or signed-axis quotient, the corpus's atom compression, or its packing code. The mathematical reduction to non-direct receivers and mandatory activations is an input to the test.

Each nonfull switch activation other than an available branch uses one join from the three-join helper budget. The initial library contains these activations and all nonempty proper switch branches. The kernel enumerates every next helper obtainable by union of two current signals. It retains the full 64-bit masks on switch assignments. Breadth-first layers deduplicate sorted helper sets only after each added signal has a recipe. It allows every new nonempty proper union as a helper, including candidates rendered useless by earlier one-atom-deficit reductions.

After every helper layer the possible paid receivers are proper nonsource unions of two library signals. The code computes their deficits, then checks whether ten are pairwise disjoint. It partitions the deficits into colors such that two deficits of the same color intersect. A packing contains at most one from each color. Branching on its last occupied color and on that color's chosen member enumerates all possible packings. The total helper-state count can exceed the earlier ledger because the permissive search retains more states.

Compile helper.cpp and controls.cpp with a C++20 compiler. For example, from this directory:
```sh
c++ -std=c++20 -O3 helper.cpp -o helper
c++ -std=c++20 -O2 controls.cpp -o controls
./controls
./helper /workspace/scratch/crown18264/verification/threshold-ten/canonical.txt selection.txt > ledger.txt
./helper /workspace/scratch/crown18264/verification/threshold-ten/canonical.txt remaining.txt > remaining-ledger.txt
```

Each ledger row gives the zero-based profile index, helper allowance, number of visited helper sets (including the empty set), and whether a packing exists. A positive result returns process status 1. The two disjoint index lists partition all 25,601 profiles. The controls test 3,000 packing decisions against exhaustive subset search, as well as positive and negative whole-library examples.
