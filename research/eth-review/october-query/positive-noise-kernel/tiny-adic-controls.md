# Hand controls for modular recovery and endpoint truncation

For the first control take L=2 with two positive unit clauses and their two COPY1 twins. The four real ports give M=4 and there are n=2 independent subdivision bits. At t=1-h, words 00 and 11 contribute 0 and 1. Each mixed word contributes (1-h²)/4. Hence F(t)=1+t-t²/2 and P(t)=2^4 F(t)=16+16t-8t². The count is one. For A=128 (the smallest power of two above 2²·2⁴), the cleared sample at t=128/129 is
$$
R=16(129)^4+16(128)(129)^3-8(128)^2(129)^2.
$$
Its residue mod 128 is 16, giving one after division by 16. Dropping the denominator-clearing factor 129⁴ leaves a fraction, so the integer residue test must follow clearing. As a boundary control, a modulus A=16 gives residue zero for this example: a strict upper bound on the encoded integer matters.

For a separate truncation control take two pairs of L=2 twin packets, all four primary units positive, with the two corresponding variable ports joined across twins by two binary COPY gates. Here N=2 and M=8. For a mixed primary word its two deviations from the population mean are +1/2 and -1/2. For a constant word both are zero. Only the four choices with both words mixed contribute to the coefficient of h⁸. Each has four squared deviations and two leading COPY coefficients of 2 after grouping the deviations, hence contributes 4/256=1/64. The full top coefficient is 1/16. The true origin count is one, so evaluating the degree-seven Taylor truncation at h=1 gives 15/16. Nearest-integer rounding succeeds on this particular control despite the exact discrepancy.

These are local kernel controls, independent of whether size two is active in a given global balanced root schedule. No execution is required for either calculation.
