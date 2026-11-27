# Two-input exclusive OR

Supply positive wires x and y in slots 0 and 1 and charge one gate for every binary AND, binary OR, and unary NOT. The complete four-row truth table is in care.json. Both inputs are binate. A common first branching vertex would have to represent the exclusive-OR pattern with one unate read-once signal of both inputs, which the pair-corner check excludes. Two branching vertices require at least three binary gates, and a descending pair requires a NOT. The expression `(x OR y) AND NOT(x AND y)` uses exactly four gates.

The application manifest pins the care rows and the certificate, sets the excluded budget to three, and includes the matching four-gate implementation.
