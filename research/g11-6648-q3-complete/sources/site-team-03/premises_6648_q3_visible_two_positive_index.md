# Visible S with two physical raw-positive dirty-reading ORs

Fix the original least size-21 L-meta-6648 TopForm hypotheses with A=x∧S the unique clean x reader, q=3, j≥3. Exactly two physical ORs have direct dirty AND pins and each has a nonempty raw other pin. A tap means the physical OR output feeds S by an OR-only path. Raw(S) is nonempty. Its possible raw labels are y=6,z=7. S accepts both singleton inputs y,z even when only one raw label is visible.

| Visible labels | Taps | Outcome |
|---|---:|---|
| both | 0 | Closed by premises_6648_q3_full_S_zero_taps.md |
| both | 1 | Closed by premises_6648_q3_full_S_one_tap.md including its final c=0 supplement |
| either or both | 2 | Closed by premises_6648_q3_two_direct_taps.md with the reviewed one-exception H bounds |
| one | 0 | Impossible: no dirty entrance in S's OR-only cone means S is a raw disjunction of the sole visible label, missing the other singleton |
| one | 1 | Partial, as below |

There are at least two original near stars in the last row: the visible x-edge and another from the common-AND/four-individual classification. Common OR is excluded at one visible. Thus at most three near residuals. Let D be the tapped donor, J the other. On H, S equals D and is clean there. At original hidden singleton v, D(v)=1. If the untapped mixed exit feeds D, call this nested. In that case allocate D-positive H pairs to D0 and JK, the two products of its raw and positive J modes. Otherwise D is one pure conjunction before cutting entrances, or its pure projected conjunction on H if the remaining exit is downstream. On D-negative H pairs, close D's mixed alternatives; J becomes pure after projection (if downstream), gives one global ordinary correction J times its shared anchored guard, and gives at most two modes at each centreless top. All projected clauses use one globally common binary exceptional support. Direct multiplicative dependencies can only decrease the number of modes. This gives n≤2c+3 if nested and n≤2c+2 otherwise.

For c≥2, any failure has U≥11, so with ≥2 near stars at most three internal H stars exist. The sparse shared-exception lemma gives U≤n+1+3. The nonnested count suffices for j≥3 and the nested for j≥4. For nested j=3 select distinct direct dirty predecessors for the c centreless roots: no raw-empty OR exists since both physical entrances are raw-positive. At most one of the three dirty gates differs from D,J. Thus when c≥2 at least one root explicitly requires D or J. On the D-negative slice a D-root vanishes and a J-root has only one mode. This saves at least one of 2c+3 batches and closes j=3 too.

At c=0 the existing F(1,2)≤4 and F(1,3)≤5 give U≤7 (nonnested) or 8 (nested). At c=1 the sparse-H proof yields F(1,4)≤6: at seven or more internal residuals there are ≤4 internal stars, hence ≤n+2=6 residuals. Also F(1,5)≤7: at eight or more internal residuals ≤3 internal stars yield ≤n+1=6. Thus U≤9 (nonnested) or 10 (nested).

Remaining parameter combinations in the single-visible single-tap branch are (c,j)=(0,3),(1,3) in the nonnested case, and (0,3),(0,4),(1,3),(1,4) in the nested case. This index makes no claim of exclusion for these six combinations. A repeated donor is included in the nonnested upper bound, which can overcount shared batches. All bounds count original residuals.
