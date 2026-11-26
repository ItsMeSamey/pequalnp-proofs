import Research.IncidenceIterate

namespace AdaptiveTerminal
open FirstGate CircuitRewire IncidenceIterate

private theorem count (m : ℕ) (D B : Finset ℕ) :
    m ≤ (Finset.range m \ (B ∪ D)).card + D.card + (B \ D).card := by
  have h := Finset.card_le_card_sdiff_add_card (s := Finset.range m) (t := B ∪ D)
  rw [Finset.card_range, ← Finset.card_sdiff_add_card] at h
  omega

theorem outside (m : ℕ) (D B : Finset ℕ) (room : D.card+B.card+1<m) (o : ℕ) :
    ∃ i < m, i ∉ D ∧ i ∉ B ∧ i ≠ o := by
  have c := count m D B
  have bc : (B \ D).card ≤ B.card := Finset.card_le_card Finset.sdiff_subset
  obtain ⟨i,hi,ne⟩ := Finset.exists_mem_ne (show 1 < (Finset.range m \ (B ∪ D)).card by omega) o
  obtain ⟨inRange,out⟩ := Finset.mem_sdiff.mp hi
  exact ⟨i,Finset.mem_range.mp inRange,fun h => out (Finset.mem_union_right _ h),
    fun h => out (Finset.mem_union_left _ h),ne⟩

theorem exists_edge (m : ℕ) (E : ℕ → ℕ → Prop) (D B : Finset ℕ)
    (room : D.card+B.card+1<m)
    (neighbors : ∀ i < m, i ∉ D → i ∉ B → ∃ j < m, j ∉ D ∧ E i j) :
    ∃ i < m, i ∉ D ∧ ∃ j < m, j ∉ D ∧ E i j := by
  obtain ⟨i,hi,iD,iB,_⟩ := outside m D B room 0
  exact ⟨i,hi,iD,neighbors i hi iD iB⟩

theorem internal {Z : Type*} (m o : ℕ) (X : ℕ → Set Z) (D B : Finset ℕ)
    (room : D.card+B.card+1<m)
    (essential : ∀ i < m, i ∉ D → i ∉ B → Essential m X o i) : m ≤ o := by
  by_contra! ho
  obtain ⟨i,hi,iD,iB,ne⟩ := outside m D B room o
  obtain ⟨u,hu,v,hv,h⟩ := essential i hi iD iB
  exact hv (h o ho ne.symm hu)

theorem lower {m s o : ℕ} {E : ℕ → ℕ → Prop} {D : Finset ℕ}
    {raw : ℕ → Gate} {X : ℕ → Set (Finset ℕ)}
    (R : Realizes m E D s o raw X) (B : Finset ℕ)
    (essential : ∀ i < m, i ∉ D → i ∉ B → Essential m X o i) :
    m ≤ s+1+D.card+(B \ D).card := by
  obtain ⟨S,within,bound,dep⟩ := IncidenceBound.support m s X (by
    intro k hk
    obtain ⟨l,r,_,op⟩ := R.normal k hk
    refine ⟨_,l,_,r,?_⟩
    rw [R.gate k hk]
    rcases op with join|meet
    · exact Or.inl (by simp [Gate.eval,join,Op.eval])
    · exact Or.inr (Or.inr (Or.inr (by simp [Gate.eval,meet,Op.eval])))) o R.bounded
  have included : Finset.range m \ (B ∪ D) ⊆ S := by
    intro i hi
    obtain ⟨ir,away⟩ := Finset.mem_sdiff.mp hi
    obtain ⟨u,hu,v,hv,h⟩ := essential i (Finset.mem_range.mp ir)
      (fun mem => away (Finset.mem_union_right _ mem)) (fun mem => away (Finset.mem_union_left _ mem))
    by_contra miss
    apply hv (dep u v ?_ hu)
    intro t ht
    exact h t (Finset.mem_range.mp (within ht)) (fun eq => miss (eq ▸ ht))
  have := Finset.card_le_card included
  have := count m D B
  omega

theorem essential_of_neighbor {m s o a c : ℕ} {E : ℕ → ℕ → Prop} {D : Finset ℕ}
    {raw : ℕ → Gate} {X : ℕ → Set (Finset ℕ)}
    (R : Realizes m E D s o raw X) (ha : a<m) (aD : a ∉ D) (hc : c<m)
    (cD : c ∉ D) (edge : E a c) (ir : ¬E c c) : Essential m X o a := by
  refine ⟨{a,c},(R.pairs a ha aD c hc cD).mpr edge,{c},?_,?_⟩
  · simpa using (fun h => ir ((R.pairs c hc cD c hc cD).mp h))
  · intro t ht ne
    rw [R.inputs t ht,R.inputs t ht]
    simp [ne]

end AdaptiveTerminal
