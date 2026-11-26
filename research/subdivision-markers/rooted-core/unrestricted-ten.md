# Score-independent certificate excluding ten elements

Write the raw chart selector z=(x<<5)|y, where x gives five dual basis selectors and y gives five primal nonbasis selectors. The designated forward and reverse selectors are a=(16<<5)|24 and b=(15<<5)|7. As in two-signature-core.md the two dimension inequalities and the even size of each shore imply that every ten-element core, regardless of gains/signatures, has clean size 4×3 and exceptions 2+1 up to duality. Both A sectors have odd size, hence 1+3. Reverse dimension sum forces rank N=2. There are four even three-bit row vectors. Their XOR must vanish by even column weights; hence their multiplicities are all odd or all even (the three nonzero vectors have just one linear dependence). At rank two this means either all four rows differ, or exactly two distinct nonzero rows are each repeated twice. Permute Y and the three clean rows of the larger A sector to obtain the three representatives below. In the all-distinct case the singleton sector row can be zero or nonzero. In the paired case choose its row as the first repeated value.

For chart rows N_i, full fundamental rows are (N_0+8,N_1+16,N_2+16,N_3+16,7). For each chart the listed five independent 10-bit selector directions span a subspace W. Its 31 nonzero members are indexed 1–31 by the bitmask of included directions (first generator low). Each indicated letter A or B certifies that toggling the corresponding direction from a or b gives another feasible raw witness. The checker tests independence and disjointness directly by multiplying the fundamental matrix and its transpose.

|Clean rows|Five generator directions|Witness letters for masks 1–31|
|---|---|---|
|0,3,5,6|32,115,230,496,527|`BBABAABBAABABBAAAAAAAAAAAAAAAAA`|
|3,0,5,6|8,115,230,496,527|`ABABBAABAAAAABBAAABBBAAABAAAABB`|
|3,3,5,5|8,83,229,496,527|`AAABBBBBABAAAAAAAAABBBBABABAAAA`|

Any linear four-bit gain map has a nonzero kernel vector in W. That direction duplicates the score of the witness indicated by the table, precluding opposite uniqueness. The argument is independent of all gains, and the final obstruction needs no missing score once the chart shape has been obtained. The absent target is used in deriving the forward and reverse dimension inequalities. This does not establish the existence of a corresponding subspace in larger charts.
