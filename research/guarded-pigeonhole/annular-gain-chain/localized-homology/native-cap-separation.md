# An acyclic four-track patch separates the cap and shortcut tests

Use rails numbered 0 through 3. In forward order the three independent native switches occupy slots (1,2,3), (0,1,2), and (0,1,3). An off gate preserves its three labels and an on gate rotates each label to the next in its listed triple. Between successive stages connect equal rail labels. The unused rail bypasses each gate. All eight settings are legal.

Writing the outputs of inputs 0,1,2,3 in order, the physical table is {0123,0231,1032,1203,1320,3102,3210}. For each of the 24 fixed return permutations and each pair of distinct input positions there is an entry whose closed orbit contains both. Thus all fixed caps pass the pairwise reachability test.

The turns 0→0 and 3→2 are individually available, have distinct inputs and outputs, and do not occur together. The only possible forward shortcut for this order would be 0→2, which no setting realizes. The shortcut test therefore fails for a genuine acyclic independent-switch patch.

Run check_native_cap_separation.py with Python 3 to trace all eight switch settings and verify every cap and marked pair.
