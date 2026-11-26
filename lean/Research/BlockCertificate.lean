import Research.IncidenceRobust

namespace BlockCertificate

theorem expanded {α : Type*} [DecidableEq α] (K : Finset α) (P Y : α → Prop) :
    (∃ p ∈ K, P p ∧ Y p) ↔
      ∀ S ⊆ K, (∃ p ∈ S, P p) ∨ (∃ p ∈ K \ S, Y p) := by
  classical
  constructor
  · rintro ⟨p,hp,hP,hY⟩ S _
    by_cases hs : p ∈ S
    · exact Or.inl ⟨p,hs,hP⟩
    · exact Or.inr ⟨p,Finset.mem_sdiff.mpr ⟨hp,hs⟩,hY⟩
  · intro clauses
    let S := K.filter (fun p => ¬P p)
    rcases clauses S (Finset.filter_subset _ _) with left|right
    · obtain ⟨p,hp,hP⟩ := left
      exact False.elim ((Finset.mem_filter.mp hp).2 hP)
    · obtain ⟨p,hp,hY⟩ := right
      obtain ⟨hK,hS⟩ := Finset.mem_sdiff.mp hp
      exact ⟨p,hK,by by_contra h; exact hS (Finset.mem_filter.mpr ⟨hK,h⟩),hY⟩

theorem before_last {α : Type*} [DecidableEq α] (K : Finset α) (L : Finset (Finset α))
    (proper : ∀ S ∈ L, S.Nonempty) :
    ∀ S ∈ L, (∃ p ∈ S, True) ∨ (∃ p ∈ K \ S, False) := by
  intro S hS
  obtain ⟨p,hp⟩ := proper S hS
  exact Or.inl ⟨p,hp,True.intro⟩

theorem private_line {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (hq : 0<q) (hn : n=q^2+q+1) (K : Finset (Fin n)) (size : K.card ≤ q+1)
    (p : Fin n) (hp : p ∈ K) : ∃ l, I p l ∧ ∀ r ∈ K, r ≠ p → ¬I r l := by
  classical
  let others := K.erase p
  let f (r : others) : Fin n := (unique p r.val (Finset.mem_erase.mp r.property).1.symm).exists.choose
  let used := Finset.univ.image f
  have usedSize : used.card ≤ others.card := by
    simpa [used] using (Finset.card_image_le (f := f) (s := Finset.univ))
  have room := Finset.card_erase_add_one hp
  have total := IncidenceRobust.lines_card I degree unique hq hn p
  have existsFresh : ∃ l ∈ IncidenceRobust.lines I p, l ∉ used := by
    by_contra! incl
    have bound := Finset.card_le_card incl
    dsimp [others] at usedSize
    omega
  obtain ⟨l,hl,unused⟩ := existsFresh
  have pl := (Finset.mem_filter.mp hl).2
  refine ⟨l,pl,?_⟩
  intro r hr ne hit
  let v : others := ⟨r,Finset.mem_erase.mpr ⟨ne,hr⟩⟩
  have fv : I p (f v) ∧ I r (f v) := (unique p r ne.symm).exists.choose_spec
  have agree := (unique p r ne.symm).unique fv ⟨pl,hit⟩
  exact unused (Finset.mem_image.mpr ⟨v,Finset.mem_univ _,agree⟩)

theorem rank {q n h : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
    (hq : 0<q) (hn : n=q^2+q+1) (K : Finset (Fin n)) (size : K.card ≤ q+1)
    (A B : Fin h → Finset (Fin n))
    (sound : ∀ i p l, p ∈ A i → l ∈ B i → I p l)
    (covers : ∀ p ∈ K, ∀ l, I p l → ∃ i, p ∈ A i ∧ l ∈ B i) : K.card ≤ h := by
  classical
  have witness (p : K) := private_line I degree unique hq hn K size p.val p.property
  let l (p : K) := (witness p).choose
  have inc (p : K) : I p.val (l p) := (witness p).choose_spec.1
  let f (p : K) := (covers p.val p.property (l p) (inc p)).choose
  have membership (p : K) : p.val ∈ A (f p) ∧ l p ∈ B (f p) :=
    (covers p.val p.property (l p) (inc p)).choose_spec
  have inj : Function.Injective f := by
    intro p r eq
    by_contra ne
    have point := (membership r).1
    rw [← eq] at point
    exact (witness p).choose_spec.2 r.val r.property
      (fun e => ne (Subtype.ext e.symm)) (sound (f p) r.val (l p) point (membership p).2)
  simpa using Fintype.card_le_of_injective f inj

end BlockCertificate
