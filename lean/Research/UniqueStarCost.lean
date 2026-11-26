import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Fintype.Card

namespace UniqueStarCost

variable {P V : Type*} [Fintype P] [DecidableEq V]

def localGates (A : P → Finset V) (K : ℕ → Finset V) (s : ℕ) (p : P) : Finset ℕ :=
  (Finset.range s).filter (fun g => 2 ≤ (K g).card ∧ K g ⊆ A p)

omit [Fintype P] in
theorem local_disjoint (A : P → Finset V) (K : ℕ → Finset V) (s : ℕ)
    (overlap : ∀ p r : P, p ≠ r → (A p ∩ A r).card ≤ 1) {p r : P} (ne : p ≠ r) :
    Disjoint (localGates A K s p) (localGates A K s r) := by
  apply Finset.disjoint_left.mpr
  intro g hp hr
  obtain ⟨big,subp⟩ := (Finset.mem_filter.mp hp).2
  have subr := (Finset.mem_filter.mp hr).2.2
  have sub : K g ⊆ A p ∩ A r := fun _ h => Finset.mem_inter.mpr ⟨subp h,subr h⟩
  have upper := (Finset.card_le_card sub).trans (overlap p r ne)
  omega

theorem global_count (A : P → Finset V) (K : ℕ → Finset V) (s q : ℕ)
    (overlap : ∀ p r : P, p ≠ r → (A p ∩ A r).card ≤ 1)
    (lower : ∀ p, q ≤ (localGates A K s p).card) :
    Fintype.card P * q ≤ s := by
  classical
  have disj : ((Finset.univ : Finset P) : Set P).PairwiseDisjoint (localGates A K s) :=
    fun p _ r _ h => local_disjoint A K s overlap h
  have all : Finset.univ.biUnion (localGates A K s) ⊆ Finset.range s := by
    intro g hg
    obtain ⟨_,_,localMem⟩ := Finset.mem_biUnion.mp hg
    exact (Finset.mem_filter.mp localMem).1
  calc
    Fintype.card P * q = ∑ _p : P, q := by simp
    _ ≤ ∑ p : P, (localGates A K s p).card :=
      Finset.sum_le_sum fun p _ => lower p
    _ = (Finset.univ.biUnion (localGates A K s)).card := (Finset.card_biUnion disj).symm
    _ ≤ s := by simpa using Finset.card_le_card all

end UniqueStarCost
