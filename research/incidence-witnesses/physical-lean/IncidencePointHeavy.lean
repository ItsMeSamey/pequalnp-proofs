import Research.SparseQueryCut
namespace IncidencePointHeavy
open CircuitRewire SparseQueryCut
open scoped BigOperators
theorem dominate_heavy {V : Type*} [DecidableEq V] (q : ℕ) (A H : Finset V) (S : Finset ℕ)
    (P : ℕ → Finset V) (star : 2*q < H.card) (width : S.card ≤ q)
    (small_or_out : ∀ i ∈ S, (P i ∩ H).card ≤ 2 ∨ ¬ P i ⊆ A) :
    ∃ l ∈ H, ∃ T : Finset V, T.card ≤ q ∧ Disjoint T A ∧
      ∀ i ∈ S, l ∈ P i → ∃ t ∈ T, t ∈ P i := by
  classical
  let small := S.filter (fun i => (P i ∩ H).card ≤ 2)
  have sc : small.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  have uc : (small.biUnion (fun i=>P i ∩ H)).card ≤ 2*q := by
    have own (i : ℕ) (hi : i ∈ small) : (P i ∩ H).card ≤ 2 := (Finset.mem_filter.mp hi).2
    calc
      _ ≤ ∑ i ∈ small, (P i ∩ H).card := Finset.card_biUnion_le
      _ ≤ ∑ _i ∈ small, 2 := Finset.sum_le_sum own
      _ ≤ 2*q := by simp; omega
  have fresh : ∃ l ∈ H, l ∉ small.biUnion (fun i=>P i ∩ H) := by
    by_contra! h
    have := Finset.card_le_card h
    omega
  obtain ⟨l,hl,away⟩ := fresh
  let active := S.filter (fun i => l ∈ P i)
  have find (i : active) : ∃ t ∈ P i.val, t ∉ A := by
    obtain ⟨ins,contains⟩ := Finset.mem_filter.mp i.property
    rcases small_or_out i.val ins with singleton|out
    · exact False.elim (away (Finset.mem_biUnion.mpr
        ⟨i.val,Finset.mem_filter.mpr ⟨ins,singleton⟩,Finset.mem_inter.mpr ⟨contains,hl⟩⟩))
    · exact Finset.not_subset.mp out
  let f (i : active) := (find i).choose
  let T := Finset.univ.image f
  have tc : T.card ≤ active.card := by
    simpa [T] using (Finset.card_image_le (f := f) (s := Finset.univ))
  have ac : active.card ≤ S.card := Finset.card_le_card (Finset.filter_subset _ _)
  refine ⟨l,hl,T,by omega,Finset.disjoint_left.mpr ?_,?_⟩
  · intro t ht
    obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp ht
    exact (find i).choose_spec.2
  · intro i hi hit
    let j : active := ⟨i,Finset.mem_filter.mpr ⟨hi,hit⟩⟩
    exact ⟨f j,Finset.mem_image.mpr ⟨j,Finset.mem_univ _,rfl⟩,(find j).choose_spec.1⟩


variable {V : Type*} [Fintype V] [DecidableEq V]
noncomputable def heavySlots (m s : ℕ) (X : ℕ → Set (Finset V)) (A H : Finset V) :=
  (Finset.range s).filter (fun g => 3 ≤ (profile X (m+g) ∩ H).card ∧ profile X (m+g) ⊆ A)

theorem physical_charge (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set (Finset V))
    (ho : o < m+s) (ordered : ∀ k<s, (raw k).left < m+k ∧ (raw k).right < m+k)
    (sem : ∀ k<s, X (m+k) = (raw k).eval X) (A H : Finset V) (r : ℕ)
    (card : 2*r < H.card)
    (input : ∀ j<m, (profile X j ∩ H).card ≤ 2 ∨ ¬ profile X j ⊆ A)
    (up : ∀ j<m+s, ∀ l : V, ∀ T : Finset V, l ∈ T → {l} ∈ X j → T ∈ X j)
    (pos : ∀ l ∈ H, ({l} : Finset V) ∈ X o)
    (neg : ∀ T : Finset V, T.card ≤ r → Disjoint T A → T ∉ X o) :
    r ≤ (heavySlots m s X A H).card := by
  classical
  by_contra! cheap
  let L := heavySlots m s X A H
  obtain ⟨S,cost,bound,cut⟩ := LocalGateCut.cut_ordered m s o raw X ho ordered sem L
  have boundary (j : ℕ) (hj : j ∈ S) : (profile X j ∩ H).card ≤ 2 ∨ ¬ profile X j ⊆ A := by
    obtain ⟨lim,h⟩ := bound j hj
    by_cases before : j<m
    · exact input j before
    · have outside := h.resolve_left before
      by_contra! hc
      apply outside
      change j-m ∈ (Finset.range s).filter _
      apply Finset.mem_filter.mpr
      have e : m+(j-m)=j := by omega
      exact ⟨Finset.mem_range.mpr (by omega),by simpa [e] using (show 3 ≤ (profile X j ∩ H).card ∧
        profile X j ⊆ A from ⟨by omega,hc.2⟩)⟩
  have width : S.card ≤ r := by change S.card ≤ (heavySlots m s X A H).card+1 at cost; omega
  obtain ⟨l,hl,T,small,dis,meet⟩ := dominate_heavy r A H S (profile X) card width boundary
  apply neg T small dis (cut {l} T ?_ (pos l hl))
  intro j hj hit
  obtain ⟨w,hw,wire⟩ := meet j hj ((mem_profile X j l).mpr hit)
  exact up j (bound j hj).1 w T hw ((mem_profile X j w).mp wire)


#print axioms physical_charge
end IncidencePointHeavy
