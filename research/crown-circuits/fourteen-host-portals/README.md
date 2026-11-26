# Composing the 507 host

The host is the disjoint union of K4 and K5 with two disjoint edges removed. Fourteen edge inputs feed nine vertex flags through nineteen binary OR gates. A 34-gate candidate with eight ANDs consequently has fifteen decoder gates, including seven ORs.

The supplied five-flag decoder uses four ORs and four ANDs. Its straightforward composition with the four-flag component and the cross-component test uses twenty decoder gates. The resulting physical circuit costs 39 (30 ORs and nine ANDs), four ORs and one AND above target. Run python replay_507_scalar.py to check every one of the 16,384 assignments. The separate bit-parallel generator is compose_507.py.

A joint decoder with fifteen gates cannot retain the eight-gate five-flag circuit as a closed subcircuit, even if it taps internal wires. Setting all five flags to zero eliminates all eight gates plus the first gate that combines the two components. The other component requires seven gates to distinguish all pairs from all triples on four flags, by duality with threshold two. Only six gates would remain. The enclosed notes describe the additional requirements for a mixed decoder. Arbitrary mixed wiring remains open.
