# Finding an induced all-odd subgraph through two specified vertices

On a finite simple graph of maximum degree five, suppose both members of every pair with at least three common neighbors have degree at most four. The algorithm decides in deterministic polynomial time whether an induced all-odd subgraph contains both named vertices. On YES it returns the original vertices of a witness. Outside the hypothesis it can return UNKNOWN.

The proof follows the canonical order of the search and repairs the first conflict in the original graph. The executable checker reproduced 510 comparisons and 172 remote-conflict cases. The independent argument and its repair controls are in the review directory.

The accompanying supplied-window construction explains why the order matters. Two connected graphs differ by one edge and have opposite answers. Every window of w successive bags in the supplied width-seven layout induces identical graphs in the two inputs. The construction uses 16 + 2w vertices. Run the following from this directory to reproduce both sets of checks.

    python common_neighbor_host_check.py
    python mixed_cap_window_check.py
