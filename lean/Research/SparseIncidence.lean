import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Prod

namespace SparseIncidence

abbrev Input (n : Nat) := (Fin n → Bool) × (Fin n → Bool)

def Extends {n} (u v : Input n) : Prop :=
  (∀ i, u.1 i = true → v.1 i = true) ∧ (∀ i, u.2 i = true → v.2 i = true)

def Upward {n} (S : Set (Input n)) : Prop :=
  ∀ ⦃u v⦄, Extends u v → u ∈ S → v ∈ S

def single {n} (i : Fin n) : Fin n → Bool := fun j => decide (j = i)

def outside {n} (r : Fin n → Fin n → Prop) [DecidableRel r]
    (b : Fin n → Bool) : Fin n → Bool :=
  fun i => decide (¬ ∃ j, r i j ∧ b j = true)

/-- The extreme tests determine every output on a sparse right-hand slice. -/
theorem sparse_slice {n q : Nat} (r : Fin n → Fin n → Prop) [DecidableRel r]
    (s : Set (Input n)) (up : Upward s)
    (pos : ∀ i j, r i j → (single i, single j) ∈ s)
    (neg : ∀ b : Fin n → Bool, Fintype.card {j // b j = true} ≤ q →
      (outside r b, b) ∉ s)
    (a b : Fin n → Bool) (sparse : Fintype.card {j // b j = true} ≤ q) :
    (a,b) ∈ s ↔ ∃ i j, a i = true ∧ b j = true ∧ r i j := by
  constructor
  · intro h
    by_contra none
    apply neg b sparse
    apply up (u := (a,b)) _ h
    refine ⟨?_, fun _ hj => hj⟩
    intro i hi
    apply decide_eq_true
    rintro ⟨j,hr,hj⟩
    exact none ⟨i,j,hi,hj,hr⟩
  · rintro ⟨i,j,hi,hj,hr⟩
    apply up (u := (single i,single j)) _ (pos i j hr)
    constructor
    · intro t ht
      have e : t = i := of_decide_eq_true ht
      simpa only [e] using hi
    · intro t ht
      have e : t = j := of_decide_eq_true ht
      simpa only [e] using hj

end SparseIncidence
