# Repair of the mixed upper clamp in the two-gate guard case

Assume the reduced one-NOT, seven-AND physical circuit has nine OR gates, its upper clamp accepts exactly singletons s,9 (s=5 or 8), the unique direct inverter reader is r=z∨D, and the guard is physically H=s∨V, V=9∨Q at distinct gates. The actual singleton 9 activates at most two OR gates. Both V and H are active.

Every actual wire active at 9 implies H on the whole input cube. Proceed in physical order. The sole active raw is 9, which implies V and H. The two active OR gates already imply H. The NOT is inactive. An active AND implies any of its active operands, giving the induction.

The gate r is cold on the actual singleton 9. Otherwise raising z leaves r unchanged and cannot affect another wire except z, whereas the upper output changes. Output cannot be z or r since the upper output rejects singleton 0. D is therefore cold and its value is independent of z, since r is the first direct reader. D is distinct from z by minimum-size duplicate-pin reduction.

No OR directly reads r. Otherwise fixing z=1 folds r and that OR, leaving at most seven ORs for the mixed upper, contrary to its eight-OR floor. The sole NOT precedes r. Every direct reader of r is therefore AND(r,P), with P different from r (duplicate pin) and z (unique direct z reader).

For every such reader whose other input P was active on singleton 9, simultaneously substitute D for its r operand. All other wires and the output index stay in place. By induction on physical gates their actual truth functions are unchanged: if P is true then H is true by the first paragraph, and r=D since z=0. This proof includes reconverging paths and uses of the modified products in later operands.

Raise z at singleton 9 in the modified circuit. Only z and r can now change. Indeed, patched r-readers still receive the unchanged, cold D, and every unpatched r-reader has an unchanged cold other operand. No other gate sees either exceptional wire. Thus the modified upper rejects singleton 9. On all singletons outside s,9 it still rejects, because H is cold there and the actual signed circuit agrees. On every edge it accepts by monotonicity in z of the modified cut and preservation of actual values. Folding r at z=1 gives an upper witness with at most eight ORs, contradicting the nine-OR floor for an upper whose only possible hot singleton is s. This last floor also covers the all-cold case. The proof excludes the nested physical guard sector; it requires distinct V,H.
