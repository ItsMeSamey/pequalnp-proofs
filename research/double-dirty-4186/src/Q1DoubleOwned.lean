import Q0Partition

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

theorem owned_partition {E H : Type*} [DecidableEq E] [DecidableEq H]
    (R : Finset E) (T : Finset H) (accepts : H → E → Prop)
    (covers : ∀ e ∈ R, ∃ h ∈ T, accepts h e) :
    ∃ owned : H → Finset E,
      (∀ h e, e ∈ owned h → e ∈ R ∧ h ∈ T ∧ accepts h e) ∧
      (T : Set H).PairwiseDisjoint owned ∧
      T.biUnion owned = R ∧ (∑ h ∈ T, (owned h).card) = R.card := by
  classical
  let owner (e : E) (he : e ∈ R) := Classical.choose (covers e he)
  have valid (e : E) (he : e ∈ R) :
      owner e he ∈ T ∧ accepts (owner e he) e := Classical.choose_spec (covers e he)
  let owned (h : H) := R.filter fun e => ∃ he : e ∈ R, owner e he = h
  have mem (h : H) (e : E) :
      e ∈ owned h ↔ ∃ he : e ∈ R, owner e he = h := by
    constructor
    · intro hmem
      exact (Finset.mem_filter.mp hmem).2
    · rintro ⟨he, eq⟩
      exact Finset.mem_filter.mpr ⟨he, he, eq⟩
  have disj : (T : Set H).PairwiseDisjoint owned := by
    intro a _ b _ hab
    apply Finset.disjoint_left.mpr
    intro e ha hb
    obtain ⟨hea, ea⟩ := (mem a e).mp ha
    obtain ⟨heb, eb⟩ := (mem b e).mp hb
    exact hab (ea.symm.trans eb)
  have unionEq : T.biUnion owned = R := by
    ext e
    constructor
    · intro he
      obtain ⟨a, _, ha⟩ := Finset.mem_biUnion.mp he
      obtain ⟨hr, _⟩ := (mem a e).mp ha
      exact hr
    · intro he
      exact Finset.mem_biUnion.mpr ⟨owner e he, (valid e he).1, (mem _ _).mpr ⟨he, rfl⟩⟩
  refine ⟨owned, ?_, disj, unionEq, ?_⟩
  · intro h e he
    obtain ⟨hr, rfl⟩ := (mem h e).mp he
    exact ⟨hr, valid e hr⟩
  · rw [← Finset.card_biUnion disj, unionEq]

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
