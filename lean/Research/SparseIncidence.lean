import Research.IncidenceBound
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Set.Prod

namespace SparseIncidence

abbrev Input (n : Nat) := (Fin n → Bool) × (Fin n → Bool)

def Extends {n} (u v : Input n) : Prop :=
  (∀ i, u.1 i = true → v.1 i = true) ∧ (∀ i, u.2 i = true → v.2 i = true)

def Upward {n} (S : Set (Input n)) : Prop :=
  ∀ ⦃u v⦄, Extends u v → u ∈ S → v ∈ S

/-- Each circuit wire is monotone under extension of the input masks. -/
theorem wire_upward {n g : Nat} (X : Nat → Set (Input n))
    (inputs : ∀ i : Fin n, X i.val = {x | x.1 i = true} ∧
      X (n + i.val) = {x | x.2 i = true})
    (gate : ∀ j < g, ∃ a < n+n+j, ∃ b < n+n+j,
      X (n+n+j) = X a ∪ X b ∨ X (n+n+j) = X a ∨ X (n+n+j) = ∅ ∨
      X (n+n+j) = X a ∩ X b)
    (o : Nat) (ho : o < n+n+g) : Upward (X o) := by
  obtain ⟨S, sub, _, dep⟩ := IncidenceBound.support (n+n) g X gate o ho
  intro u v huv h
  apply dep u v _ h
  intro i hi
  have bound := Finset.mem_range.mp (sub hi)
  by_cases low : i < n
  · rw [(inputs ⟨i, low⟩).1]
    exact huv.1 _
  · let k : Fin n := ⟨i-n, by omega⟩
    have eq : n+k.val = i := by dsimp [k]; omega
    rw [← eq, (inputs k).2]
    exact huv.2 _

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
