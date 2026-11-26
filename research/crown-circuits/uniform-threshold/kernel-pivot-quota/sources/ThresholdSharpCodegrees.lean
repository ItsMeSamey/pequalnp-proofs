import ThresholdC4
import Mathlib.Data.Nat.Choose.Basic
namespace ThresholdSharpCodegrees
open scoped BigOperators
variable {I : Type*} [DecidableEq I]

/-- For one unordered four-set, b is the number of its perfect matchings.
J counts cycles and N counts nonedge diagonal presentations. -/
theorem box {b N : Nat} (cap : b≤3) (small : b≤1 → N=0)
    (two : b=2 → N≤2) (clique : b=3 → N=0) :
    2*b.choose 2≤3*(b-1) ∧ N≤2*(b-1) := by
  have cases' : b=0 ∨ b=1 ∨ b=2 ∨ b=3 := by omega
  rcases cases' with rfl | rfl | rfl | rfl <;> simp_all [Nat.choose]

/-- Fine loss needs only the nonedge diagonal charge; the global second moment
may use a larger collection of exceptional matchings. -/
theorem nonedge_moment (nonedges : Finset I) (c : I → Nat) (w L : Nat)
    (population : 2*nonedges.card≤w^2)
    (charge : (∑ p ∈ nonedges, (c p).choose 2)≤2*L) :
    let D := ∑ p ∈ nonedges, c p
    2*D^2≤w^2*(4*L+D) := by
  intro D
  have hd := sq_sum_le_card_mul_sum_sq (s:=nonedges) (f:=c)
  have sqid (z : Nat) : z^2=2*z.choose 2+z := by
    induction z with
    | zero => decide
    | succ k ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      nlinarith
  have sumid : (∑ p ∈ nonedges, c p^2)=2*(∑ p ∈ nonedges, (c p).choose 2)+D := by
    simp only [sqid,Finset.sum_add_distrib,Finset.mul_sum,D]
  have cap : (∑ p ∈ nonedges, c p^2)≤4*L+D := by omega
  calc
    2*D^2≤2*(nonedges.card*(∑ p ∈ nonedges, c p^2)) := Nat.mul_le_mul_left 2 hd
    _=(2*nonedges.card)*(∑ p ∈ nonedges, c p^2) := by ring
    _≤_ := Nat.mul_le_mul population cap

/-- Adjacent and nonadjacent unordered vertex pairs. The match-loss ledger
supplies moment and charge, with L measured in unordered candidate pairs.
The exact finite nonedge loss is S-A, and the nonedge population is retained. -/
theorem moments (edges nonedges : Finset I) (c : I → Nat) (w L : Nat)
    (population : 2*(edges.card+nonedges.card)≤w*(w-1))
    (moment : (∑ p ∈ edges, c p^2)+(∑ p ∈ nonedges, c p^2)≤
      (∑ p ∈ edges, c p)+(∑ p ∈ nonedges, c p)+6*L)
    (charge : (∑ p ∈ nonedges, (c p).choose 2)≤2*L) :
    let A := ∑ p ∈ edges, c p
    let D := ∑ p ∈ nonedges, c p
    let S := A+D
    A^2≤edges.card*(S+6*L) ∧
      2*D^2≤(w*(w-1)-2*edges.card)*(4*L+D) := by
  intro A D S
  have ha := sq_sum_le_card_mul_sum_sq (s:=edges) (f:=c)
  have hd := sq_sum_le_card_mul_sum_sq (s:=nonedges) (f:=c)
  have sqid (z : Nat) : z^2=2*z.choose 2+z := by
    induction z with
    | zero => decide
    | succ k ih =>
      rw [Nat.choose_succ_succ]
      simp only [Nat.choose_one_right]
      nlinarith
  have sumid : (∑ p ∈ nonedges, c p^2)=2*(∑ p ∈ nonedges, (c p).choose 2)+D := by
    simp only [sqid,Finset.sum_add_distrib,Finset.mul_sum,D]
  constructor
  · apply ha.trans
    apply Nat.mul_le_mul_left
    dsimp [S,A,D]
    omega
  · have ds : (∑ p ∈ nonedges, c p^2)≤4*L+D := by omega
    have count : 2*nonedges.card≤w*(w-1)-2*edges.card := by omega
    calc
      2*D^2 ≤ 2*(nonedges.card*(∑ p ∈ nonedges, c p^2)) := Nat.mul_le_mul_left 2 hd
      _ = (2*nonedges.card)*(∑ p ∈ nonedges, c p^2) := by ring
      _ ≤ _ := Nat.mul_le_mul count ds
end ThresholdSharpCodegrees
