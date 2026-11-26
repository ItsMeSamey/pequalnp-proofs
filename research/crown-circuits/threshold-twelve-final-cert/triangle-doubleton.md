# A doubleton in the pure triangle

Let Q,A,B form the pure triangle, with Q the quartet and A the doubleton. The third group B is cubic. In a minimum size-28 seven-AND representative, A and B are unshared, and their single AND readers are distinct by the small-group lemma. Delete the two labels QA and AB. Exactly five gates disappear, leaving a minimum size-23 ten-input circuit. The AND reading A is the only one-sided dark AND.

The pure tree for B still has two raw labels, QB and its outside label. Its reader remains the same AND. If that AND went dark it would be a second one-sided dark AND, since B is nonzero. Removing it by redundancy or pruning the remaining cherry would save a sixth gate, violating the ten-input lower bound. Each of the two remaining raw labels has at least two consumers, since a sole reader in their common cherry would make adding it to the other singleton undetectable.

Delete those two inputs in turn from the ten-input circuit. The four raw incidences already consume its entire saving budget against the eight-input bound of 19. Yet the AND reading the cherry also supplies a one-sided dark charge. Its other operand cannot turn identically false under the joint deletion, since it would then imply the cherry everywhere and the AND would be redundant. This contradiction eliminates the orbit.
