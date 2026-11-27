# Conditional size minimum at eleven mixed gates on cut 199

Combined proof outline for the fixed-cut, fixed-mixed-count theorem. Counts below describe the component producers’ evidence. A hash identifies bytes, not a proof receipt.

## Statement and model

On vertices 0 through 10 take the positive Boolean function which accepts exactly assignments containing an entire edge from the following list.

```
09  0–10  14  18  25  2–10  36  37  48  4–10  58  59  67  6–10  79  89
```

Here two adjacent digits denote two single-digit endpoints. The left variables are 0,1,2,6,7 and the right variables are 3,4,5,8,9,10. Consider single-output straight-line circuits of binary AND and OR of earlier wires, starting from these raw variables. Both pins count, including repeated pins. Cost counts each physical gate once including shared gates. Correctness means agreement on all 2,048 assignments. A mixed gate has raw ancestors on both sides; a pure gate has ancestors on one side. Let M be the mixed count and P the pure count. The proposed combined conclusion is that the minimum of M+P **conditional on M=11** is 22. No lower bound of 22 for larger mixed counts follows.

## Global normalization at fixed M

Choose a realization with least P among *all* realizations with M=11. The output depends on both sides. Discarding dead gates preserves its value. By the separate general lower bound M≥11 for this cut, no mixed gate can disappear under trimming. Therefore every gate is live. If a pure gate equals an earlier wire on its own side for every assignment, replace every reader pin and any output reference by that wire, delete the gate and renumber. In an AO circuit each wire has nonempty syntactic ancestry. The set of sides reaching every surviving gate is consequently unchanged by induction along its pins. This yields the same M and smaller P, even if distinct boundary wires become one wire read twice. The argument permits deleting full-cube pure aliases before counting ports. A cofactor alias only saves a gate in the restricted producer. Choosing a minimizer within the tree subcase alone would leave an unjustified assumption that bypass preserves its tree.

Team 07 also reports a direct check of the duplicate-left-port alternative through three paid gates in the one-hit branch. Of 80 order-compatible multisets, 32 survive the cotree condition and zero survive the first parity stage. This provides an alternate exclusion for that specific branch.

## Incidence split

Let p,q count distinct left and right pure wires feeding mixed gates, including raw wires. The 19 distinct left residuals and 17 distinct right residuals force p,q≥5. The eleven live mixed gates have 22 input pins. Every boundary port and every mixed gate is used at least once when the output tap is counted. Hence 12−p−q counts excess uses with multiplicity. At zero excess the mixed decoder is a read-once tree. Its Karchmer–Wigderson leaf partition, tested on the sixteen edges versus maximal independent sets, requires at least six leaves of each color by the rank bound, so p=q=6. Positive excess leaves precisely (5,5), (6,5) and (5,6).

| Branch | Necessary condition and exclusion of P≤10 | Component evidence |
|---|---|---|
| (5,5) | Split codes, donor placements and forced leaf rectangles exclude all 2,018 projected signatures. | two-donors-split-codes |
| (6,5) | With raw 3 isolated, four varying ports must work on both faces. With raw 3 used by a paid gate, pinning loses a gate. Lower-code consistency leaves 11,178 of 12,248 true upper-face tuples. Donor and rectangle tests reduce the final budget-eight test to ten portfolios, with no feasible producer. | one-pure-repeat-q5, one-mixed-repeat-q5, one-donor-split-codes |
| (5,6) | Two active ports at singleton 3. Anchoring and producer tests force raw 3 and a terminal OR with raw 3 at the putative budget. Lower-face compatibility excludes every split, granting arbitrary monotone values of the other OR operand. | one-donor-six-right, nontree-pure-cost |
| (6,6), one active port | The left bank costs at least four gates. Across budgets through four, order and tree constraints leave 277 banks, necessary parity conditions leave eight and full row-mask extension leaves one bank costing four. The separate right bound of seven suffices. | left-bank-cotree, left-general-parity, parity-full; right bound below |
| (6,6), two active ports | The four remaining upper-face truth tables must admit a single read-once tree, with constants and pruning varying across eight backgrounds. None of the 180 remaining portfolios is produced in eight gates. | tree-two-hit/verify.cjs directly binds corrected face, common-tree test and producer test |

A right port is active if true on the input consisting of vertex 3 alone. At least one is active because the empty right input and singleton 3 have different profiles. Nine upper-face profiles require at least four varying bits, permitting at most two active ports. These alternatives exhaust the tree case.

For the one-hit right bound the rank-six leaf columns are independent. Internal-right edges have the same all-right completed row, hence select a common subset of right leaves. Each independent right input extends to a maximal global negative so one of these leaves rejects it. Their conjunction equals the internal-right graph function. At 3=0 this requires six paid producer gates even with the final conjunction free. If raw 3 enters any right gate, the first such gate disappears on pinning, giving seven. Otherwise raw 3 is a port and five ports produced on the other variables must jointly provide the factor and distinguish all directed residual comparisons across both faces. The six-gate joint enumeration and rank-six inactivity obstruction for raw 4 must both be applied to this case. Each surviving five-port candidate contains raw 4. On the seven positive global masks 513,1025,258,36,136,1088,544 versus all 24 maximal independent sets, raw 4 is always false. Its leaf rectangle is therefore empty. The partial right-color matrix on these samples has minimum completion rank at least six over GF(2), by exclusion of every two-dimensional row kernel. In that row order the allowed nonzero row dependencies are 3,34,49,51,57,59,61,63,117,119,121,123,125,127. The XOR of two distinct entries never belongs to the list. Five nonempty rectangles cannot represent this matrix. The free-conjunction bound by itself gives only six.

In the two-hit tree, pin 3=1. The common four-leaf upper tree is obtained by pruning the fixed decoder, preserving the gate operations and allowing constants at its leaves across the eight left backgrounds. The four required outputs are nonraw. An eight-gate producer has at most four additional helpers. Directly available required outputs can be scheduled as soon as available, and all possible helpful paid intermediates are covered by exhaustive AND/OR extensions. This gives nine paid upper-face gates. At least one of the two active ports is computed because only one raw variable is active. Its dependence on 3 forces a direct use of 3 in a paid gate which simplifies away under the pin. Thus P_right≥10. Six distinct left ports from five raw inputs require P_left≥1.

Every branch gives P≥11. The archived 22-gate witness has eleven mixed gates and realizes the stated edge function. Together these imply the conditional minimum if the listed premises pass review. The historical non-tree report stops before the separate tree analyses. Neither its anchored 180 count nor the older both-face 7,355-tuples generator certifies the two-hit tree step.

## Snapshot and evidence dependencies

General mixed bound, port incidence, KW rank, non-tree branches, left-bank filters, right cost and two-hit enumeration are separate dependencies. The scalar replay and witness supply only the upper bound. The following SHA-256 values pin sources and inputs for review. Paths without a leading slash are relative to the team-11 scratch directory.

```text
8d565fbfd40f83c16b44c39e84cd8167625c0b1d441e6bad1ab2bc8a1227de77  cut199-eleven.md
d80b01bfd171648d5dee480dd6efab0c821ea3bf79f75b3eeae0be35873df51c  one-edge-cut-obstruction.md
778930980bf6ef332375105d088a18849b6d699943df9d1c8c40d45ffecdd70f  cut199_ports.js
d2372f341ffd775d1f307d3ed8f02c7dcc476ca0a55a392353203a0d05e65ce2  cut199-kw-short.cjs
cdb555351c003c67c540244bd898968213c659196482f909e10734840aca0dda  cut199-kw-rank-six.cjs
7a16190b32354a6c541c3d32778f3e86b3dc54c5c6522a0691bb5feee15bf3b1  cut199-tree-port-factors.md
46ef8ea9f31cc8e38b85ac2bc2ea342b7bf1b69afe54766552972cb4c1d3cb36  cut199-nontree-pure-cost.md
aaf8a4d8ab5d7e9357a5c099436f176d751d094fc446aa1bc87cd47f982fb1eb  cut199-nontree-audit-v1.zip
1c0e74207f9eabf6318d921272ed6d2ec80406e8ea0caa2c1ff2f35bd8ed4aaa  cut199-two-donors-split-codes.cjs
ded22d731c3555d243aa2f239bb12a5b9dcc869c3636e43eb81e8fa61ba56643  cut199-two-disjoint-donors.cjs
f94694319359bed8559aaf558593e4575fa5be87cc45b0f4a2a776b2438af6ff  cut199-one-pure-repeat-q5.cjs
6d9941b93fc738a20b47d37aa29065fb2d012d422b44af5e8b8ebda490dbcbf1  cut199-one-mixed-repeat-q5.cjs
08d4046e780d24897afb992275cdb368556d87e1d18f970a8dd4c481bf03dd6d  cut199-one-donor-split-codes.cjs
650cb9ce4d2815ab23d552aa4468ad6640e482f7f4d38ca8a08d35be0320f945  cut199-one-donor-six-right.cjs
cbf5c05828f4c69a5a638e79b4ecf0183534d55eb5663ce86787da1010738a6c  cut199-right-four-on-face.cjs
06420fe498d0a1c11fba3466118b8d6fc48019d18634619bbdd204317977ee38  cut199-free-and-right-six.cjs
dff1145ab2ae57737238859994fae465d225145415bc2f11beedc0a295b2437f  cut199-six-right-joint.cjs
474bdfa95a79dc4c6cb1b55ae8e882ad82239688b84dbe8350010db22262f805  cut199-left-bank-cotree.cjs
5966d935147f66edab3d4fd8b3c94b08f8c65f3dc6735a85fd4e39d52e13aa28  cut199-left-bank-cotree-survivors.json
31f0dc318a15af7121b1985dae1deed9ec7abc61f1c0d558f60f2058658c4c34  cut199-left-general-parity.md
182997c34a591964ef84d51f31dffe0a7c0354098b5cf388a4d81bea4f46c304  cut199-left-general-parity.cjs
4c0ec018b815e78754cc452d69d6f61dd284db38731897236897a3a851fdc011  cut199-left-general-parity.json
13712193fc961954a1f220b16dd15b71180d03ff3c586ec285688ee6f1988bab  cut199-parity-full.cjs
7704f39c78267bed778c18d309afc4e0ea25a633fee42699b4b0ae3f32b340d7  cut199-parity-full.json
df024cbcbef04c38674e69e190cdfe43e5e0504ffa82aa50aec23873fb38917e  cut199-tree-two-hit/verify.cjs
9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b  cut199-tree-two-hit/issued18272.txt
67b568329b5ccfe106ec3d1b38ca0056fec0052223332dc81f298c1d3a531c87  cut199-size22-mixed11.json
e40ab207497ef4f0c0c96165c4139894bb995443923cfb1b1361217897a408d3  scalar_cut199_pair.py
9ec4bd7fce25977e79676fd87f567c30812b34f80a264e9df1a9aeb6d972f84b  pnp-official-18272-issued.lean
a7bd50f3c295d45bb887b9381a6070029576d893020bce4dfc9324ba83a017f1  cut199-tree-two-hit/PROOF.md
0df024747fcf9f1bebcba3dc352d5d62f1ffc64dbb78075716114662c83655a8  cut199-tree-two-hit/replay.json
45e33a4f4f89d91acea01da64e0eedb23e0e8e45512dc532aa38766871f98a8e  cut199-tree-two-hit/SHA256SUMS
3c98166474d4a49cc926cebe6f0c8237fdd56e9c0fb8f16f6078e1a9d416abc9  cut199-tree-two-hit.zip
ed24a2a323fafc96f81b424fcc2fd637af4beead00e4bfe88148840007a29879  cut199_alias_check.py
2f6caa1257bbec1d2a24b0df7fe2bca3cd171172564b059616d0b62fcef1b4d0  cut199-tree-right-cost.cjs
```
