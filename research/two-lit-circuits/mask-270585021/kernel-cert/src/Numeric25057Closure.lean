import Numeric25057
namespace Numeric25057

def Covered (table : Array Key) (n : Nat) : Prop :=
  ∀ i, i < n → ∃ proof, checkRow table i proof = true

theorem covered_zero (table : Array Key) : Covered table 0 := by
  intro i hi
  exact False.elim (Nat.not_lt_zero _ hi)

theorem covered_succ {table : Array Key} {n : Nat} {p : List Nat}
    (prior : Covered table n) (row : checkRow table n p = true) : Covered table (n+1) := by
  intro i hi
  rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hi) with h | h
  · exact prior i h
  · subst i
    exact ⟨p, row⟩

theorem children_checked {table : Array Key} {ks : List Key} {ws : List Nat}
    (h : checkChildren table ks ws = true) (k : Key) (hk : k ∈ ks) :
    ∃ w, checkChild table k w = true := by
  induction ks generalizing ws with
  | nil => simp at hk
  | cons a tail ih =>
    cases ws with
    | nil => simp [checkChildren] at h
    | cons w rest =>
      have hh := Bool.and_eq_true_iff.mp h
      rcases List.mem_cons.mp hk with rfl | ht
      · exact ⟨w, hh.1⟩
      · exact ih hh.2 ht

theorem row_children_checked {table : Array Key} {i b t : Nat}
    {s : State} {proof : List Nat} (hi : table[i]? = some (b,t,s))
    (hc : checkRow table i proof = true) :
    s.contains goal = false ∧ ∀ k ∈ next b t s, ∃ w, checkChild table k w = true := by
  simp only [checkRow, hi, Bool.and_eq_true] at hc
  constructor
  · simpa using hc.1
  · exact children_checked hc.2

end Numeric25057
