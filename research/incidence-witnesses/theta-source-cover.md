# Positive cover credit for warm-to-cold receivers

Fix the dominating theta with k=q+1 arms, D its deleted raw coordinates, and all residual independent two-by-two masks. Copy the cold normalization from full-theta-physical-credit.md. Its c0 sources are cold ANDs with two warm operands. After suppressing all cold inputs in the middle network, evaluate each source on its two rebuilt warm operands. Every source rejects every required negative; their union covers all 3k positive flags by the earliest-cold argument. Let t be the minimum number of rebuilt sources covering all flags. Then 1≤t≤min(c0,3k).

Cold sources no longer feed the middle network or one another. Keep just t source ANDs and combine them with t−1 ORs. The all-source construction used c0 ANDs and c0−1 ORs, saving another 2(c0−t) slots. Dead warm inputs may be left in the count. One must use rebuilt-source values, since suppression can change original positive values.

Let c1 count cold gates with exactly one warm and one cold input. These are ANDs. Deleted sole-read raws have distinct such compensators; denote their number by H_D. The single restriction then gives
   δ ≥ F_C + E_D + (c1−H_D) + 2(c0−t).
Equivalently, if J counts all warm operand slots entering cold gates, including warm raw sources, then J=c1+2c0 and
   δ ≥ F_C + E_D + J − H_D − 2t.
The first version has nonnegative terms. The second prices both types of warm-to-cold receivers while accounting for those that repair flags. Original reconvergence is unrestricted. Independently audited by /root/incidence/audit and /root/incidence/rank.
