import Research.IncidenceRobust

namespace ProtectedIncidence
open IncidenceRobust

theorem dual_unique {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (join : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (hq : 0 < q) (hn : n = q^2+q+1)
    (l k : Fin n) (lk : l ≠ k) : ∃! p, I p l ∧ I p k := by
  classical
  let F := fun p => (lines I p).erase l
  have size (p) (hp : p ∈ points I l) : (F p).card = q := by
    have inc : l ∈ lines I p := by simpa [points,lines] using hp
    simp [F, Finset.card_erase_of_mem inc, lines_card I degree join hq hn]
  have disj : (points I l : Set (Fin n)).PairwiseDisjoint F := by
    intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro t hta htb
    obtain ⟨tl,at'⟩ := Finset.mem_erase.mp hta
    have bt := (Finset.mem_erase.mp htb).2
    obtain ⟨_,_,only⟩ := join a b ne
    exact tl ((only t ⟨(Finset.mem_filter.mp at').2,(Finset.mem_filter.mp bt).2⟩).trans
      (only l ⟨(Finset.mem_filter.mp ha).2,(Finset.mem_filter.mp hb).2⟩).symm)
  have sub : (points I l).biUnion F ⊆ Finset.univ.erase l := by
    intro t ht
    obtain ⟨p,_,hf⟩ := Finset.mem_biUnion.mp ht
    exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hf).1, Finset.mem_univ _⟩
  have card := Finset.card_biUnion disj
  rw [Finset.sum_congr rfl size, Finset.sum_const, points_card I degree] at card
  have eq : (points I l).biUnion F = Finset.univ.erase l := by
    apply Finset.eq_of_subset_of_card_le sub
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
    rw [card]
    change n - 1 ≤ (q+1)*q
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_two]
    omega
  have hk : k ∈ (points I l).biUnion F := by
    rw [eq]
    exact Finset.mem_erase.mpr ⟨lk.symm, Finset.mem_univ _⟩
  obtain ⟨p,hpl,hpk⟩ := Finset.mem_biUnion.mp hk
  have hp : I p l ∧ I p k := ⟨(Finset.mem_filter.mp hpl).2,
    (Finset.mem_filter.mp (Finset.mem_erase.mp hpk).2).2⟩
  refine ⟨p,hp,?_⟩
  intro a ha
  by_contra ne
  obtain ⟨_,_,only⟩ := join a p ne
  exact lk ((only l ⟨ha.1,hp.1⟩).trans (only k ⟨ha.2,hp.2⟩).symm)

end ProtectedIncidence
