# Coverage of the issued G11 surplus inequality

Use the exact issued circuit and selected sets. Let j≥3 count junk ANDs, c centreless tops, q the ORs in orN outside lam, and U the original residual edge count. The required inequality follows from U≤j+2c+q by the issued balance. A proof using a projected graph must bound original residual edges or separately verify transfer of the selected hypotheses. The three reader columns below refer to the sole reader of input 3. The 21-gate lower bound and the separate two-OR exclusion justify this reader split only under the exact least TopForm hypotheses.

| Region | Sole OR | Sole dirty AND | Sole clean AND |
|---|---|---|---|
| q=0, all c | Accepted L18392 if U≥3, otherwise j≥3 suffices | Same | Same |
| q=1, all c | Bound U≤2c+j+1 | Bound U≤2c+j+1 | Pure/impure and raw-support split gives U≤2c+4≤2c+j+1 |
| q=2, c=0 | U≤j+2 | U≤j+2 | Pure, singleton-raw and both-raw impure cases all covered |
| q=2, c≥1 | U≤2c+j+2 | U≤2c+j+2 | U≤2c+j+2, counting physical ORs that directly read dirty ANDs |
| q≥3, all c | Open in general | Open in general | Open in general |

Whole q=2 aggregate: 6648-q2-complete.md, SHA d777f85b3f238e86d48fd87a08298985ab3d82de31d61476323daf579b960305, dependency premises_6648_raw_empty_two_positive_mixers.md SHA 3620a8f3e6fe84f601e3301b5bb60ffc6ded598d979db9d252f0f704455f6dac. Whole q=1 aggregate: 6648-q1-complete.md, SHA 916cb247ae32995f75443c0d9bf71cffaec4664294f43a023fc805ccbea11d4c. Whole c=0,q=2 aggregate: 6648-c0q2-complete.md, SHA dab1b65d992d75f9f88c958c29bfe820f4455ae4044df3db9184edad37b85714. The size-21 private-donor exclusion applies across open rows in the sole-OR column; the donor must have another reader. A two-pure-exception result can also cover some q=2 circuits when the separate purity hypotheses are established. None of these research aggregates is a combined Lean proof.

## Finite parameter region still requiring a structural argument

There are 16 graph edges. If t=0, Lambda is empty because each Lambda gate witnesses an ordinary top. Every clean OR has only clean constituents; following them reaches a clean AND because all singleton inputs are rejected. Hence no clean OR can feed another AND by TopForm. Rebuilding the output from the c top wires uses c−1 OR gates. Least size 21 then gives j+2c+q≥22, and U≤16 suffices. For t≥1 at least one pair is starred. Exactly one starred edge forces P≥15 by 6648-single-star.md, so U=15 is covered. Every remaining candidate must have at least two starred edges, U≤14, 3≤q≤10, 0≤c≤floor((10−q)/2), and 3≤j≤13−2c−q. It must also have U≥j+2c+q+1. These are necessary numeric conditions, not assertions that a circuit exists.

The gate identity is 2t+lambda=22−P for the original least size-21 circuit. Its clean OR aggregation spans its distinct t+c clean AND tops and can be rebuilt with exactly t+c−1 gates. The accepted size score additionally gives t+P≤U+6. Neither establishes the original theorem for all q≥3. For example c=0,q=3,j=3,t=4,U=7 is a purely arithmetic profile meeting these upper bounds but failing U≤P. The independent-star-cover cutoff for a particular candidate can impose additional necessary conditions. Selected-set existence, actual shared circuit wiring, TopForm and leastness remain essential when looking for a counterexample.

No combined source for the entire official theorem has been verified.
