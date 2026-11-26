import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace BoundedOccurrence

variable {Clause Var : Type*} [Fintype Clause] [DecidableEq Var]

/-- A family with at least three variables per clause and each variable in at most
three clauses has a system of distinct representatives. -/
theorem matching (vars : Clause → Finset Var)
    (width : ∀ c, 3 ≤ (vars c).card)
    (occ : ∀ v : Var, (Finset.univ.filter (fun c => v ∈ vars c)).card ≤ 3) :
    ∃ f : Clause → Var, Function.Injective f ∧ ∀ c, f c ∈ vars c := by
  classical
  apply (Finset.all_card_le_biUnion_card_iff_existsInjective' vars).mp
  intro s
  let r := fun (c : Clause) (v : Var) => v ∈ vars c
  have lo : ∀ c ∈ s, 3 ≤ ((s.biUnion vars).bipartiteAbove r c).card := by
    intro c hc
    apply (width c).trans
    apply Finset.card_le_card
    intro v hv
    exact (Finset.mem_bipartiteAbove r).mpr ⟨Finset.mem_biUnion.mpr ⟨c, hc, hv⟩, hv⟩
  have hi : ∀ v ∈ s.biUnion vars, (s.bipartiteBelow r v).card ≤ 3 := by
    intro v _
    apply le_trans _ (occ v)
    apply Finset.card_le_card
    intro c hc
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, ((Finset.mem_bipartiteBelow r).mp hc).2⟩
  have h := Finset.card_mul_le_card_mul r lo hi
  omega

/-- Each clause is satisfied when one of its variables takes the Boolean value
prescribed by its literal's sign. -/
theorem satisfiable (vars : Clause → Finset Var) (sign : Clause → Var → Bool)
    (width : ∀ c, 3 ≤ (vars c).card)
    (occ : ∀ v : Var, (Finset.univ.filter (fun c => v ∈ vars c)).card ≤ 3) :
    ∃ assignment : Var → Bool, ∀ c, ∃ v ∈ vars c, assignment v = sign c v := by
  classical
  obtain ⟨f, hinj, hmem⟩ := matching vars width occ
  let assignment := fun v => if h : ∃ c, f c = v then sign h.choose v else false
  refine ⟨assignment, fun c => ⟨f c, hmem c, ?_⟩⟩
  have h : ∃ d, f d = f c := ⟨c, rfl⟩
  simp [assignment, h, hinj h.choose_spec]

end BoundedOccurrence
