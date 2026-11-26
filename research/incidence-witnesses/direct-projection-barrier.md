# Gate-count barrier for direct raw identification

Let t be the number of retained sites. A direct identification writes one target raw per site. To improve a 2n−4 bound by merely projecting the terminal graph after charging two per deleted site would require target minimum greater than 2t−4.

Ordinary threshold two on m labels needs t≥2m−2: any pair must have adjacent opposite-shore copies, hence at most one point-only label and one line-only label exist. Prefix ORs, one AND per subsequent input and their output OR cost 3m−5≤2t−4 for m≥3. For m=2,t=2 the isolated edge costs one. The ordinary domination-and-degree elimination cannot finish with a nonempty batch onto that edge: all deleted vertices neighbor an endpoint, and edges between deleted leaves would make a 4-cycle, so they have degree one.

One-hot crown needs t≥2m by incomparable rows and columns. Pair m row/column raws by OR and compute threshold two at cost at most 4m−5<2t−4.

For full-cube shore-respecting crown, four singly represented labels on each shore would supply two singleton rows and two singleton columns disjoint from those row labels, forcing a 4-cycle. Thus t≥3m−3 for m≥4. Prefix and suffix unions compute every all-but-one column OR in 3m−6 gates. Row products and their collector cost 2m−1 more, giving at most 5m−7≤2t−4. The m=3 upper bound is eight with t≥6, and m=2 costs three with t≥4.

Independent audit confirmed the dimension and arithmetic bounds. They concern only the projected target. A source circuit could cost more, but automatic savings from identifying copies are unjustified.
