# Sharing bound for arbitrarily contaminated point singleton pools

In the reduced circuit from fractional-line-cover-pinning.md fix M≥1 bounding every actual wire's fractional line cover for its point singleton support S_g. Put T=floor(2M)+1 and h_l=max_g |S_g∩l|. Then

    (2M) times (number of physical OR gates)
       ≥ sum over geometric lines l of max(0,ceil(h_l/(T−1))−1).

To see this, fix l with h_l≥T. From a maximizing actual wire trace back while its l-support has size at least T. At an OR follow both input slots; at an AND choose just one parent deterministically. Process each reached wire once. A selected AND parent contains all the child's accepted point singletons, while OR gives their union. The support of the terminal wires thus covers the initial h_l points. Each terminal covers ≤T−1, so there are at least ceil(h_l/(T−1)) distinct terminals. Raw inputs are terminal. The resulting DAG is connected and has P+2B outgoing slots for P one-parent and B two-parent nonterminals; connectivity on P+B+L distinct vertices implies L≤B+1, including ties and reconvergence. Hence the indicated number of distinct ORs are traced for this l.

For any physical OR gate, use a fractional geometric cover u of total at most M for its point singleton set. If a line l contains k≥T of its point singletons then k≤k u_l+M−u_l, since each other line meets l once. Thus u_l≥1/2 and at most 2M lines can trace that OR. Summing the per-line charges establishes the physical inequality. In particular, if a positive fraction of all lines have h_l≥cq for fixed c>0, the original circuit has Ω(Nq/(log q)²) gates after using the fixed-cap normalization M=O(log q). This charge requires no condition on contamination outside l, no predefined collection of star outputs, and no fanout bound. It does require large line coverage on the actual normalized wires; this has not been shown for every circuit.
