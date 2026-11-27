import Q1DoubleFourSlots

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

/-- Select one endpoint of each Y-edge, and include the given hub as one of them. -/
theorem cover_four_and_hub {V : Type*} [DecidableEq V] (label : Pos → V)
    (fresh : V → V → Prop) (p : Pos)
    (hub : ∀ a b, fresh a b → label p = a ∨ label p = b) :
    ∃ S : Finset V, S.card ≤ 2 ∧
      (∀ i : Bool, label (i,false) ∈ S ∨ label (i,true) ∈ S) ∧
      (∀ a b, fresh a b → a ∈ S ∨ b ∈ S) := by
  let z (i : Bool) := label (i, if i=p.1 then p.2 else false)
  let S : Finset V := {z false,z true}
  have mem (t : Bool) : z t ∈ S := by cases t <;> simp [S]
  have hp : label p ∈ S := by simpa [z] using mem p.1
  refine ⟨S, ?_, ?_, ?_⟩
  · by_cases eq : z false = z true <;> simp [S,eq]
  · intro i
    have hi := mem i
    change label (i, if i=p.1 then p.2 else false) ∈ S at hi
    cases h : (if i=p.1 then p.2 else false) <;> simp only [h] at hi
    · exact Or.inl hi
    · exact Or.inr hi
  · intro a b hab
    rcases hub a b hab with left | right
    · exact Or.inl (left ▸ hp)
    · exact Or.inr (right ▸ hp)

/-- A hub covers at most one edge of a matching, irrespective of its orientation. -/
theorem hub_matching_card {V : Type*} {r : ℕ} (pt : Fin r → Bool → V) (v : V)
    (sep : ∀ i j, i ≠ j → ∀ k l, pt i k ≠ pt j l)
    (covers : ∀ i, v = pt i false ∨ v = pt i true) : r ≤ 1 := by
  by_contra! large
  let i : Fin r := ⟨0,by omega⟩
  let j : Fin r := ⟨1,by omega⟩
  have ij : i ≠ j := by intro eq; have := congrArg Fin.val eq; change 0=1 at this; contradiction
  rcases covers i with hi | hi <;> rcases covers j with hj | hj <;>
    exact sep i j ij _ _ (hi.symm.trans hj)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
