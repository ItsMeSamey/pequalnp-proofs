# Six binary gates cannot suffice on a six-flag basis

On the four-by-four quotient, using indices 0,1,2,3 for raw classes 0,3,4,default, the row masks in little-endian column order are 5,4,9,10. The column masks are 5,8,3,12. All row and column patterns differ, hence at least three available raw flags per shore must be used. Choose any basis of exactly three rows and three columns, with omitted base classes r,c respectively.

A flagged row i is binate if its support and the base row support are incomparable. For a fixed column, base and row i differ only in the i input, so differences in both directions give genuine opposite sensitivities on the promise. Define binate columns symmetrically. If a used input has no fanout node in its forward cone it has a unique path to the output and hence is unate: every AND/OR preserves order and each NOT reverses it. The same holds for read-once formulas with arbitrary negations.

In a live circuit with six input leaves, B binary gates and any number of unary NOT gates, total fanout excess (including output observer) is B−5. For B≤6 there is at most one wire W of fanout two and no higher fanout. Binate variables exist for every base, hence W exists. All binate leaves lie in the fan-in cone of W (including W itself). This cone is a read-once formula in its raw inputs because W is the only branching wire. Each input in the cone influences the output only through W. Set every nonbinate flag to zero. The circuit now factors through one bit W, so the output, as a constant or unary function of W, is unate in each remaining flag on the restricted promise.

That restriction retains the base row, the incomparable rows, the base column, and the incomparable columns. In each base choice (r,c) the retained rows still include the following witness i, whose support is incomparable with the base row on the retained columns. Witnesses by r=0,1,2,3 and c=0,1,2,3 respectively:
  (2,3,2,2)
  (2,2,2,2)
  (0,1,0,0)
  (0,0,0,0)
These entries can be checked by restricting the displayed row masks to base and incomparable columns. This contradicts the unateness conclusion.

For seven used flags six binary gates give no branching at all. On the shore with exactly three flags there remains at least one row or column incomparable with its base, even when all four opposite flags are supplied. Eight flags require at least seven binary decoder gates. Thus a nine-gate decoder budget with at least two NOTs cannot include even one separately paid merged raw-class flag (one remaining decoder binary would have been spent), and with at least three NOTs no six-flag decoder works. This statement assumes the specified quotient basis and the stated per-merged-flag price, not free access to arbitrary derived wires.
