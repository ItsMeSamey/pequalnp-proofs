# Equality pins couple disjoint four-color shells

A color consists of two Boolean coordinates. Given a matching and side constraints equating pairs of individual raw coordinates (possibly across coordinate positions), deciding whether the matching has a proper coloring satisfying the pins is NP-complete. The matching may instead be a disjoint union of copies of any fixed four-colorable graph with a distinguished edge. No other graph is required.

Reduce Boolean AND/NOT circuit satisfiability with one asserted output. Construct a separate edge for each row below. Names in its two ordered endpoint pairs denote Boolean coordinates. Use equality pins to connect all occurrences of each name along a path. This uses no constants, negated pins or long affine rows. A repeated name within an endpoint or edge means separate physical coordinates connected in its name class.

| Purpose | First color | Second color |
| --- | --- | --- |
| Choose Boolean rails | (a,a) | (b,a) |
| Complement rails for each wire x | (x,a) | (x̄,a) |
| First half of z=x AND y | (x,b) | (a,z) |
| Second half of z=x AND y | (x,y) | (b,z̄) |

The first edge forces a≠b. Interpret the value a as false and b as true. The wire edge enforces the complementary pair x,x̄. For a NOT gate z=¬x merge the names z and x̄, and for the output merge its name with b. Merge before wiring the paths. If x is false the first AND edge forces z false; the second edge is automatically proper. If x is true the second edge forces y≠z̄, equivalently y=z; the first edge is automatically proper. Conversely every satisfying Boolean assignment, with a=0,b=1, fills every row properly. Each color certificate and its pins can be checked in linear time.

This is a linear-size construction. The side-pin graph on the physical color bits is a disjoint union of paths, so each bit participates in at most two pins, and all those rows are independent over GF(2). It is the joint occurrence of wire classes at proper-edge constraints that realizes arbitrary circuit interactions. If the matching edges are replaced by shells, any two prescribed distinct colors on the distinguished edge extend to the whole shell by globally permuting a fixed proper coloring independently in each copy. Membership in NP still holds.

The claim requires cross-shell raw-coordinate equality pins. With no side pins a disjoint union of the fixed shells has an immediate coloring. The reduction establishes unrestricted hardness with growing pin rank; it gives no hardness claim at fixed rank or bounded width of the combined constraint interaction.
