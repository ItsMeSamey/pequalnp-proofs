# Size 33 and four extracted degree-one products

Assume a 33-gate normalized residual separator of minimum live size, then minimum distinct raw width, then minimum total singleton-support size. The previously published raw-width theorem (archive f7fc2e7c…) gives n ≤ s−9 ≤ 24 for this normalized circuit. The official assertion is equivalent to the existence of a residual separator of size at most 33; the official minimum is one more than the residual minimum.

The degree-one normalization (f90d2d65…) permits a terminal product or a sole OR entry for each present raw singleton among 2,8,16,32. Consider the case in which all four are separate terminal products. Their deletion removes four AND gates and four collector OR gates. Each removed positive must now be rejected by the core, since otherwise its product could have been deleted. The signed minor 31546414… has 24 required positives and 239 maximal negatives. Nine singleton points and seven raw line flags survive. The six possible additional composite point sources are 129,354,523,1046,2092,4160. The original n≤24 permits at most four; the total bank count is 57.

The low-owner package e2983fc0… evaluates all 57 banks. It excludes every case with at most six mandatory line owners and all fifteen banks of size 20 in the core. In the seven-owner case the remaining bank counts by number of composite sources are 1,6,15,20. The cut and charge package 14818869… excludes these 42, and c35b9f4c… independently checks the signed comparisons and bin costs. The structural assembly and fresh 42-bank replay have independent review.

Thus a minimum normalized representative at residual size 33 cannot have four separately extracted degree-one products. Cases with fewer extracted products remain. The normalized residual minimum is still in [33,34] and the unrestricted official minimum in [34,35].

Run python verify.py in extracted t4-low.zip and peeled-seven.zip separately. Run python signed.py in the extracted t4-seven-dark.zip. Dependency hashes follow.
