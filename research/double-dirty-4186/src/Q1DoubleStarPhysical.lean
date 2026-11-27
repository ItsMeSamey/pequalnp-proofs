import Q1DoubleStar
import Q1DoubleStarTight
import Q1DoubleStarLayout
import Q1DoubleStarExternal

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private
open scoped BigOperators
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

/-- Distinct indexed physical pin occurrences give the side-slot balance by a
single injection, even when different pins carry the same raw wire. -/
theorem physical_slot_balance {I : Type*} [Fintype I] {a : ℕ} (k : I → ℕ)
    (slot : ∀ i, Fin (k i) → Fin a)
    (distinct : Function.Injective (fun q : Σ i, Fin (k i) => slot q.1 q.2)) :
    ∃ x, a = x + ∑ i, k i := by
  have le := Fintype.card_le_of_injective _ distinct
  simp only [Fintype.card_sigma,Fintype.card_fin] at le
  exact ⟨a-(∑ i, k i),by omega⟩

theorem star_price_original {I : Type*} [Fintype I] {a b w x : ℕ}
    (k p : I → ℕ) (balance : a=x+∑ i,k i) :
    x+b+w+∑ i, (k i+p i+1) = a+b+w+∑ i, (p i+1) := by
  simp only [Finset.sum_add_distrib]
  omega

/-- Physical one-arm star. Each external root reuses its specified A-side
slots and has separate private slots. Guard slots have the same wires at A
and B. Disjoint assignment refers to actual residual graph edges. -/
theorem physical_star_charge {I : Type*} [Fintype I] {a b w r s x : ℕ}
    (k p h : I → ℕ) (leaks : 2 ≤ Fintype.card I) (ka : a=x+∑ i,k i) (hb : 2≤b) (hw : 0<w)
    (hk : ∀ i, 2≤k i) (hp : ∀ i, 0<p i) (four : NoFourCycle G)
    (A : Fin a → Clause n) (B : Fin b → Clause n) (W : Fin w → Clause n)
    (slot : ∀ i, Fin (k i) → Fin a) (Z : ∀ i, Fin (p i) → Clause n)
    (PA : Batch G C A W r) (PB : Batch G C B W s)
    (PY : ∀ i, Batch G C (A ∘ slot i) (Z i) (h i))
    (ab : ∀ j l c d, s(PA.pt j c,PA.pt j (!c)) ≠ s(PB.pt l d,PB.pt l (!d)))
    (ae : ∀ i j l c d, s(PA.pt j c,PA.pt j (!c)) ≠ s((PY i).pt l d,(PY i).pt l (!d)))
    (be : ∀ i j l c d, s(PB.pt j c,PB.pt j (!c)) ≠ s((PY i).pt l d,(PY i).pt l (!d)))
    (ee : ∀ i j, i≠j → ∀ u l c d,
      s((PY i).pt u c,(PY i).pt u (!c)) ≠ s((PY j).pt l d,(PY j).pt l (!d))) :
    2*r+2*s+∑ i, 2*h i ≤ x+b+w+∑ i, (k i+p i+1) := by
  classical
  apply one_arm_multi_leak k p h r s x b w leaks hb hk hp (fun i => (PY i).power)
  · intro i hi eq
    have tight {nh : ℕ} (P : Batch G C (A ∘ slot i) (Z i) nh)
        (two : nh=2) (ex : ∀ j l c d, s(PA.pt j c,PA.pt j (!c)) ≠ s(P.pt l d,P.pt l (!d))) :
        r≤1 := by
      subst nh
      exact tight_external_batch P four eq (hk i) PA.pt (fun j => PA.edges j false) PA.sep
        (fun leaf j => PA.hits (.inl (slot i leaf)) j) (fun j l d => ex j l false d)
    exact tight (PY i) hi (ae i)
  · exact (Q0Transversal.twice_le_pow s).trans PB.power
  · intro rich
    rw [← ka]
    obtain ⟨v,nearA,anchors⟩ := rich_batch_anchor PA rich four
    have classify (i) := classify_external (PY i) four v (by have := hk i; omega) (hp i)
      (fun c y hy => anchors (.inl (slot i c)) y hy) PA.pt PA.edges nearA PA.sep (ae i)
      (fun c j => PA.hits (.inl (slot i c)) j)
    by_cases deficient : ∃ i, h i=2 ∧ p i=2 ∧ 2^r ≤ k i
    · exact Or.inl deficient
    right
    let T := Finset.univ.filter fun i => p i+1 < 2*h i
    have paid (i) (hi : i ∉ T) : 2*h i ≤ p i+1 := by simpa [T] using hi
    have active (i : T) : 0<h i.val ∧ ∀ j d, G.Adj v ((PY i.val).pt j d) := by
      rcases classify i.val with ok|near|defect
      · have := (Finset.mem_filter.mp i.property).2; omega
      · exact near
      · exact (deficient ⟨i.val,defect⟩).elim
    refine ⟨T,paid,?_⟩
    let ext (i : T) : Projected G C := ⟨_,_,_,_,_,PY i.val⟩
    let left : Projected G C := ⟨_,_,_,_,_,PA⟩
    let right : Projected G C := ⟨_,_,_,_,_,PB⟩
    have extEx (i j : T) (ij : i≠j) : (ext i).exclusive (ext j) :=
      ee i.val j.val (fun eq => ij (Subtype.ext eq))
    by_cases little : s≤2
    · rw [if_pos little]
      have pool := pooled_star_layout (B := Unit) (Base := Fin a ⊕ Fin w) four v
        (fun _ => left) ext (literals A W) (fun _ c => c)
        (fun i c => Sum.inl (slot i.val c)) (fun _ _ => rfl) (fun _ _ => rfl)
        (fun _ => by dsimp [left]; omega) (fun i => (active i).1) (fun _ => nearA)
        (fun i => (active i).2) (fun i j ne => (ne (Subsingleton.elim i j)).elim)
        extEx (fun _ i => ae i.val)
      change (∑ _ : Unit, 2^r) + (∑ i : T, 2^(h i.val)) ≤ Fintype.card (Fin a ⊕ Fin w) + ∑ i : T, p i.val at pool
      rw [Finset.sum_coe_sort T (fun j => 2^(h j)), Finset.sum_coe_sort T p] at pool
      simpa using pool
    · rw [if_neg little]
      have nearB := rich_shared_neighborhood PB (by omega) four (.inr ⟨0,hw⟩) v
        (fun y hy => (anchors (.inr ⟨0,hw⟩) y hy).1)
      let centers : Bool → Projected G C := fun t => if t then right else left
      let phys : Fin a ⊕ (Fin b ⊕ Fin w) → Clause n := Sum.elim A (Sum.elim B W)
      let cid (t : Bool) : Fin (centers t).a ⊕ Fin (centers t).w → Fin a ⊕ (Fin b ⊕ Fin w) := by
        cases t with
        | false => exact Sum.elim Sum.inl (fun c => Sum.inr (.inr c))
        | true => exact Sum.elim (fun c => Sum.inr (.inl c)) (fun c => Sum.inr (.inr c))
      have ok (t : Bool) (c) : phys (cid t c) = literals (centers t).left (centers t).right c := by
        cases t <;> cases c <;> rfl
      have position (t : Bool) : (centers t).inside v := by cases t <;> first | exact nearA | exact nearB
      have pos (t : Bool) : 0 < (centers t).count := by
        cases t
        · change 0 < r; omega
        · change 0 < s; omega
      have cex (i j : Bool) (ne : i≠j) : (centers i).exclusive (centers j) := by
        have ab' : left.exclusive right := ab
        cases i <;> cases j <;> first | exact (ne rfl).elim | exact ab' | exact Projected.exclusive_symm ab'
      have ex (t : Bool) (i : T) : (centers t).exclusive (ext i) := by
        cases t <;> first | exact ae i.val | exact be i.val
      have pool := pooled_star_layout four v centers ext phys cid
        (fun i c => Sum.inl (slot i.val c)) ok (fun _ _ => rfl) pos (fun i => (active i).1)
        position (fun i => (active i).2) cex extEx ex
      rw [Fintype.sum_bool] at pool
      first | change 2^s + 2^r + (∑ i : T, 2^(h i.val)) ≤ Fintype.card (Fin a ⊕ (Fin b ⊕ Fin w)) + ∑ i : T, p i.val at pool
            | change 2^r + 2^s + (∑ i : T, 2^(h i.val)) ≤ Fintype.card (Fin a ⊕ (Fin b ⊕ Fin w)) + ∑ i : T, p i.val at pool
      rw [Finset.sum_coe_sort T (fun j => 2^(h j)), Finset.sum_coe_sort T p] at pool
      simp only [Fintype.card_sum,Fintype.card_fin] at pool
      omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
