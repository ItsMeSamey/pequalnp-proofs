import Q1DoubleFourSlots

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

/-- Four two-vertex supports are all four patterns, counted by actual occurrence.
The rejection premise ranges over all four transversals, including the complements
of the selected endpoints. -/
theorem physical_patterns {V : Type*} [DecidableEq V] (label : Pos → V)
    (inj : Function.Injective label) (L : Fin 4 → Finset V)
    (pair : ∀ c, ∃ u v, L c = {u,v})
    (hit : ∀ c i, label (i,false) ∈ L c ∨ label (i,true) ∈ L c)
    (reject : ∀ t : Pattern, ∃ c, label (false,!t.1) ∉ L c ∧ label (true,!t.2) ∉ L c) :
    ∃ f : Fin 4 ≃ Pattern, ∀ c a, a ∈ L c ↔ inSlot label (f c) a := by
  classical
  choose pick misses using reject
  have picks (t : Pattern) : label (false,t.1) ∈ L (pick t) ∧ label (true,t.2) ∈ L (pick t) := by
    have left := hit (pick t) false
    have right := hit (pick t) true
    have m := misses t
    rcases t with ⟨x,y⟩
    cases x <;> cases y <;> simp_all
  have unique : Function.Injective pick := by
    rintro ⟨a,b⟩ ⟨c,d⟩ eq
    have h := picks (a,b)
    rw [eq] at h
    have m := misses (c,d)
    cases a <;> cases b <;> cases c <;> cases d <;> simp_all
  let equiv := Equiv.ofBijective pick ((Fintype.bijective_iff_injective_and_card pick).mpr ⟨unique,by decide⟩)
  refine ⟨equiv.symm, ?_⟩
  intro c a
  obtain ⟨t,rfl⟩ := equiv.surjective c
  change a ∈ L (equiv t) ↔ inSlot label (equiv.symm (equiv t)) a
  rw [equiv.symm_apply_apply]
  change a ∈ L (pick t) ↔ _
  obtain ⟨u,v,h⟩ := pair (pick t)
  obtain ⟨h₀,h₁⟩ := picks t
  have ne : label (false,t.1) ≠ label (true,t.2) := fun eq => by simpa using congrArg Prod.fst (inj eq)
  have shape : L (pick t) = {label (false,t.1), label (true,t.2)} := by
    rw [h] at h₀ h₁ ⊢
    simp only [Finset.mem_insert, Finset.mem_singleton] at h₀ h₁
    rcases h₀ with h₀ | h₀ <;> rcases h₁ with h₁ | h₁
    · exact (ne (h₀.trans h₁.symm)).elim
    · rw [h₀,h₁]
    · rw [h₀,h₁,Finset.pair_comm]
    · exact (ne (h₀.trans h₁.symm)).elim
  rw [shape]
  simp only [Finset.mem_insert,Finset.mem_singleton]
  constructor
  · rintro (rfl | rfl)
    · exact ⟨(false,t.1),rfl,rfl⟩
    · exact ⟨(true,t.2),rfl,rfl⟩
  · rintro ⟨⟨i,j⟩,hj,rfl⟩
    cases i
    · exact Or.inl (congrArg (fun k => label (false,k)) hj)
    · exact Or.inr (congrArg (fun k => label (true,k)) hj)

/-- Restrict the four-slot bijection to the actual shared occurrences. -/
theorem shared_patterns {V : Type*} [DecidableEq V] {label : Pos → V}
    (L : Fin 4 → Finset V) (f : Fin 4 ≃ Pattern)
    (hf : ∀ c a, a ∈ L c ↔ inSlot label (f c) a) (J : Finset (Fin 4)) :
    ∃ T : Finset Pattern, T.card = J.card ∧
      ∀ a b, (∀ j ∈ J, a ∈ L j ∨ b ∈ L j) →
        ∀ t ∈ T, inSlot label t a ∨ inSlot label t b := by
  classical
  refine ⟨J.image f, Finset.card_image_of_injective _ f.injective, ?_⟩
  intro a b h t ht
  obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp ht
  exact (h j hj).imp (hf j a).mp (hf j b).mp

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
