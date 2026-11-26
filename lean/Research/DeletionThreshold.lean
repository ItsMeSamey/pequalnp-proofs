import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace DeletionThreshold

/-- Combine an incidence moment bound with the gate cost of deletion. -/
theorem combine {q n d bad gates : Nat} (small : d < q^2)
    (moment : q^2 * bad ≤ d * (q + bad))
    (cost : 2*n+d ≤ gates+1+bad) :
    2*n+d ≤ gates+1+(d*q)/(q^2-d) := by
  have h := Nat.sub_add_cancel (Nat.le_of_lt small)
  have rew : (q^2-d)*bad+d*bad = q^2*bad := by
    rw [← Nat.add_mul, h]
  have prod : bad*(q^2-d) ≤ d*q := by
    rw [Nat.mul_add] at moment
    rw [Nat.mul_comm]
    omega
  have cap := (Nat.le_div_iff_mul_le (Nat.sub_pos_of_lt small)).mpr prod
  omega

/-- Sum the bounds for the two parts of the bipartite graph, allowing
each part to have a different number of deleted neighbors. -/
theorem both_parts {q l r a b : Nat}
    (left : q^2 * a^2 ≤ l * a * (q+a))
    (right : q^2 * b^2 ≤ r * b * (q+b)) :
    q^2 * (a+b) ≤ (l+r)*(q+(a+b)) := by
  have cancel (t k : Nat) (h : q^2 * t^2 ≤ k*t*(q+t)) :
      q^2*t ≤ k*(q+t) := by
    by_cases ht : t = 0
    · simp [ht]
    have h' : t*(q^2*t) ≤ t*(k*(q+t)) := by
      calc
        t*(q^2*t) = q^2*t^2 := by ring
        _ ≤ k*t*(q+t) := h
        _ = t*(k*(q+t)) := by ring
    exact Nat.le_of_mul_le_mul_left h' (by omega)
  rw [Nat.mul_add, Nat.add_mul]
  exact Nat.add_le_add
    ((cancel _ _ left).trans (Nat.mul_le_mul_left l (by omega)))
    ((cancel _ _ right).trans (Nat.mul_le_mul_left r (by omega)))

set_option maxRecDepth 4096 in
set_option maxHeartbeats 1000000 in
/-- Finite consequence conditional on the gate-elimination bound.
Choosing q²−17q deletions balances the two loss terms near order 288. -/
theorem through288 {q n gates : Nat} (lo : 201 ≤ q) (hi : q ≤ 288)
    (order : n = q^2+q+1)
    (bound : let d := q^2-17*q
             2*n+d ≤ gates+1+(d*q)/(q^2-d)) :
    n*q ≤ 100*gates := by
  have arithmetic : ∀ i : Fin 289, let q := i.val
      let n := q^2+q+1
      let d := q^2-17*q
      201 ≤ q → n*q + 100*(1+(d*q)/(q^2-d)) ≤ 100*(2*n+d) := by decide
  have h := arithmetic ⟨q, by omega⟩ lo
  change (q^2+q+1)*q+100*(1+((q^2-17*q)*q)/(q^2-(q^2-17*q))) ≤
    100*(2*(q^2+q+1)+(q^2-17*q)) at h
  subst n
  dsimp only at bound
  omega

end DeletionThreshold
