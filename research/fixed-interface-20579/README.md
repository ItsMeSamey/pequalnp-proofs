# Two fixed circuit replacements for the 32-by-32 graph

For the specified 21 input signals, every scalar continuation requires at least 28 gates. The fixed prefix and interface cost 137 + 6 gates, giving a total of at least 171. The projected-tail package includes the structural deductions, a finite certificate, and its checker. The table, structural cases, and certificate received independent review and the frozen checker passed a fresh extraction.

For the separately specified five-output replacement with 141 retained gates, the checker regenerates exactly 117 donor banks. Its certified replacement lower bounds are 30 gates for 37 banks, 31 for 32 banks and 32 for 48 banks. Every bank exceeds the 29 gates available in this layout.

The two results apply to their respective interfaces. Existence of a different circuit of at most 170 gates remains open.
