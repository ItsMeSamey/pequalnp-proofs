import Q1DoubleWeighted
import Q0Transversal

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open scoped BigOperators

/-- Each pooled root is clean. Each global choice of one endpoint per
assigned edge is independent. A shared physical slot has the same support
at all its roots, so missing it fixes at most one local orientation at each. -/
theorem pooled_physical_slots {V R L : Type*} [Fintype R] [Fintype L] (G : SimpleGraph V)
    (batch : R → ℕ) (positive : ∀ i, 0 < batch i)
    (pt : ∀ i, Fin (batch i) → Bool → V) (owners : L → Finset R) (contains : L → V → Prop)
    (hits : ∀ l i, i ∈ owners l → ∀ j, contains l (pt i j false) ∨ contains l (pt i j true))
    (clean : ∀ i (S : V → Prop), (∀ l, i ∈ owners l → ∃ v, S v ∧ contains l v) →
      ∃ u v, S u ∧ S v ∧ G.Adj u v)
    (indep : ∀ (t : ∀ i, Fin (batch i) → Bool) i j k m,
      ¬ G.Adj (pt i j (t i j)) (pt k m (t k m))) :
    (∑ i, 2^(batch i)) ≤ Fintype.card L := by
  classical
  let X (i : R) := Fin (batch i) → Bool
  let miss (l : L) (i : R) := (Finset.univ : Finset (X i)).filter
    (fun t => ∀ j, ¬ contains l (pt i j (t j)))
  have uniq (l : L) (i : R) (hi : i ∈ owners l) : (miss l i).card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro t ht u hu
    funext j
    have ht' := (Finset.mem_filter.mp ht).2 j
    have hu' := (Finset.mem_filter.mp hu).2 j
    have hit := hits l i hi j
    cases et : t j <;> cases eu : u j <;> simp_all
  have rejected (t : ∀ i, X i) (i : R) :
      ∃ l, i ∈ owners l ∧ ∀ k ∈ owners l, t k ∈ miss l k := by
    let S (v : V) := ∃ k j, pt k j (t k j) = v
    have hm : ∃ l, i ∈ owners l ∧ ∀ v, S v → ¬ contains l v := by
      by_contra! h
      obtain ⟨u,v,⟨k,j,rfl⟩,⟨k',m,rfl⟩,adj⟩ := clean i S h
      exact indep t k j k' m adj
    obtain ⟨l,hl,absent⟩ := hm
    exact ⟨l,hl,fun k _ => Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun j =>
      absent _ ⟨k,j,rfl⟩⟩⟩
  have two (i : R) : 2 ≤ Fintype.card (X i) := by
    have hi := positive i
    obtain ⟨k,hk⟩ : ∃ k, batch i = k+1 := ⟨batch i-1,by omega⟩
    simp [X,hk,pow_succ]
    exact Nat.one_le_pow _ _ (by decide)
  simpa [X] using weighted_leaf_count X two owners miss uniq rejected

/-- An outsider satisfies all private slots of a deficient mixed external
top. For r mutually independent edges whose endpoints cannot see that
outsider, the shared block must reject every orientation. -/
theorem deficient_shared_slots {V L P : Type*} [Fintype L] (G : SimpleGraph V)
    (z : V) {r : ℕ} (pt : Fin r → Bool → V)
    (shared : L → V → Prop) (privateSlot : P → V → Prop)
    (hits : ∀ l i, shared l (pt i false) ∨ shared l (pt i true))
    (outside : ∀ i b, ¬ G.Adj z (pt i b))
    (indep : ∀ (t : Fin r → Bool) i j, ¬ G.Adj (pt i (t i)) (pt j (t j)))
    (allPrivate : ∀ p, privateSlot p z)
    (clean : ∀ S : V → Prop, (∀ l, ∃ v, S v ∧ shared l v) →
      (∀ p, ∃ v, S v ∧ privateSlot p v) → ∃ u v, S u ∧ S v ∧ G.Adj u v) :
    2^r ≤ Fintype.card L := by
  classical
  apply Q0Transversal.pow_le_card pt shared hits
  intro t
  by_contra! hit
  let S (v : V) := v=z ∨ ∃ i, pt i (t i)=v
  have h₁ (l : L) : ∃ v, S v ∧ shared l v := by
    obtain ⟨i,hi⟩ := hit l
    exact ⟨_,Or.inr ⟨i,rfl⟩,hi⟩
  obtain ⟨u,v,hu,hv,adj⟩ := clean S h₁ (fun p => ⟨z,Or.inl rfl,allPrivate p⟩)
  rcases hu with rfl|⟨i,rfl⟩ <;> rcases hv with rfl|⟨j,rfl⟩
  · exact G.loopless.irrefl _ adj
  · exact outside _ _ adj
  · exact outside _ _ adj.symm
  · exact indep t i j adj

/-- For a mixed two-edge batch with two private slots, each private slot
contains the outside endpoint. The two transversals through x have different
rejecting slots since each slot meets the interior edge. -/
theorem deficient_private_contains {V : Type*} (x z : V) (f : Bool → V)
    (privateSlot : Bool → V → Prop)
    (hitsInner : ∀ p, privateSlot p (f false) ∨ privateSlot p (f true))
    (hitsOuter : ∀ p, privateSlot p x ∨ privateSlot p z)
    (reject : ∀ b, ∃ p, ¬ privateSlot p x ∧ ¬ privateSlot p (f b)) :
    ∀ p, privateSlot p z := by
  obtain ⟨p,hpx,hpf⟩ := reject false
  obtain ⟨q,hqx,hqt⟩ := reject true
  have ne : p ≠ q := by
    rintro rfl
    exact (hitsInner p).elim hpf hqt
  intro k
  have e : k=p ∨ k=q := by cases k <;> cases p <;> cases q <;> simp_all
  rcases e with rfl|rfl
  · exact (hitsOuter _).resolve_left hpx
  · exact (hitsOuter _).resolve_left hqx

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
