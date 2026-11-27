# Counting source groups once

Continue the model and notation of large-group-boundary.md. Write L for the number of minimal-large internal ORs and J for the number of flattened OR groups containing at least one. In each group containing j such sources, follow their unique paths to its top. Different source nodes cannot be ancestors of other sources along these OR paths, as largeness persists through ORs. The connecting tree contains at least j−1 ORs with two large inputs. Globally the number of two-large-input internal nodes was bounded by L+G+2p−B; hence removing at least L−J such ORs gives A−u≤J+G+2p−B. In bounding V by large boundary occurrences, at most J groups have an internal source. Consequently
```
V≤2J+3G+4p−2B.
```

Each high group v of degree d≥4 has extra charge at least d+3 in 6V−5R, by the edge-weight proof in large-group-boundary.md. Choose one minimal-large source in each source group. Its ≥t+1 distinct tokens come from the ordinary raw slots of that group and designated private tokens, with no token occurrence shared by two groups. In high source groups d+3≥t+4 minus the number of their private tokens. In low source groups at most three ordinary slots exist, so each costs at least t−2 private tokens. With γ=(t+4)/(t−2), this proves
```
sum over high groups (d+3) ≥ (t+4)J−γu.
```
It follows that 5R≤(8−t)J+18G+24p−12B+γu. For 3≤t≤8 substitute J≤[2(n−p)−u]/(t+1). A sufficient surplus condition is
```
(7t−11)(n−p) > [6t−3+(t+1)γ]u+(t+1)(18G+24p−12B).
```

Use periodic current-sole-OR hoists from protected-asymptotic-surplus.md at block=384. Geometric marks plus the theta remain permanent. Let B count just the unmarked current sole-ORs separately protected. They number at most min(2z−m,768). Each literal reset leaves no such sole-OR unmarked; charge any subsequent pruning separately. The symmetric starting promise can be reduced to b=3+floor(k/384), leaving at least 3 after all resets. Mark newly threatened sites and their three neighbors using H=q−8−4−floor(k/384). Then p≤geom+B and u≤S₀+2z−m−B. The adverse coefficient of B is 13t+4−(t+1)γ, positive at every integer t=3,…,8. The previous block maxima remain valid.

Using blocks of width 32, check-source-groups-408.py verifies the official bound through order 408. At order 407 the maximum batch is 6 and the sum of the caps is 56936. At order 408 these numbers are 8 and 77360. At order 409 the program first fails at stage block 10656; it checks this specific envelope only.
