# Profile 21567 operand polarity

The two 19-gate monotone controls use the signed axis permutation (0,4,2,1,3,5). Under the original Lean selector, true chooses the left operand and false chooses the right operand. The archived native replay chooses the left operand on false. Thus native word w has the same physical selected operands as Lean word w XOR 63. Permuting six axes commutes with complementing all six bits. Native sign 0 consequently translates to Lean sign 63 for this permutation.

Both fixed-route evaluations reproduce all 1,024 graph rows, all 64 original signed resolutions, all ten receiver masks and sorted raw socket classifications. The essential two-user control has direct vertices 2,3,5,6. The other control has direct vertices 1,3,5. Only the former exercises the d4 branch.

The fixed_controls_lean63.py and audit_direct.py checks are independent Python reimplementations of the original selection rule. Their attached outputs are native receipts. SixH3FlatOriginalDirect21567 and SixH3FlatMoveDirect21567 give the corresponding Lean source interfaces with the actual gate and chosen operand. rowCheck supplies the signed permutation for each candidate. Kernel validation of the complete d4 exclusion remains pending.

This supplement accompanies the immutable source-class21567-v2.zip (SHA-256 03cd24775bacdcee38ba77f81c1aec1426f75731a56d855553c1301468a548d6).
