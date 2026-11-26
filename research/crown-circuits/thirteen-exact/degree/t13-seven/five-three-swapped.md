# Three pure branches, fanout-three OR and fanout-two AND

Write m≤7 for the OR support and q≤2 for branching quartets. The shared AND singleton credit cancels its support debit. Therefore 49≤35+q+2m−(6−c). Necessarily q=2, c=4 and m=7. The AND must be dirty, since a clean shared AND would leave three other dirty debits, and both other dirty outputs have support one.

No nonraw joins remain outside the collector. The shared OR has one nonraw term and at most four raw slots, so it cannot take a singleton-hot output as its source. If it takes a branch it requires at least three raws and the five other branch exits need one each. If it takes the shared AND, all six branch exits need one each. In either case both other dirty outputs need at least two raw occurrences each to reach their first AND operand of support at least three. Trees originating at these separate source occurrences are disjoint up to the next shared root or AND. The resulting lower bounds twelve and ten both exceed the nine mixed occurrences left by two quartets.

With three additional fanout-two roots, at least two must be ORs. Otherwise the possible OR yields at most eight singleton credits and the shared ANDs cancel their own debits, leaving at most 35+2+8=45.
