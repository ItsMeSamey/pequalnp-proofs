import Q1DoubleTrianglePair

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

variable {n a w : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
variable {A : Fin a → Clause n} {W : Fin w → Clause n}

/-- Mark all nonunique occurrences and label each remaining occurrence
by the two omitted endpoints of its unique rejecting assignment. -/
theorem small_occurrences (four : NoFourCycle G) (P : Batch G C A W 2) :
    ∃ bad : Finset (Fin a ⊕ Fin w), ∃ row : (Fin a ⊕ Fin w) → Bool → Bool,
      bad.card ≤ 2*(a+w-4) ∧
      (∀ l, l ∉ bad → literals A W l =
        Finset.univ.image (fun i => P.pt (finTwoEquiv.symm i) (row l i))) ∧
      (∀ l l', l ∉ bad → l' ∉ bad → row l = row l' → l = l') := by
  classical
  let rej (l : Fin a ⊕ Fin w) (t : Fin 2 → Bool) := ∀ i, P.pt i (t i) ∉ literals A W l
  have one l t u (ht : rej l t) (hu : rej l u) : t=u := by
    funext i
    have h1 := ht i
    have h2 := hu i
    have hit := P.hits l i
    cases et : t i <;> cases eu : u i <;> simp only [et,eu] at h1 h2 ⊢ <;> first | rfl | exact (hit.elim h1 h2).elim | exact (hit.elim h2 h1).elim
  obtain ⟨bad,cap,good⟩ := nonunique_slots rej P.reject one
  let pick l : Fin 2 → Bool := if h : l ∉ bad then (good l h).choose else fun _ => false
  let row l (i : Bool) := !(pick l (finTwoEquiv.symm i))
  have spec (l) (hl : l ∉ bad) : rej l (pick l) ∧ ∀ z, rej z (pick l) → z=l := by
    simpa [pick,hl] using (good l hl).choose_spec
  refine ⟨bad,row,by simpa using cap,?_,?_⟩
  · intro l hl
    let t := pick l
    let mate i := P.pt i (!(t i))
    have full : literals A W l = Finset.univ.image mate := by
      refine unique_slot_exact four (by decide : 2 ≤ 2) (fun i => P.pt i (t i)) mate
        ?_ ?_ ?_ ?_ (literals A W) l (P.anchor l) ?_ ?_ ?_ ?_
      · intro i j eq; by_contra ne; exact P.sep i j ne _ _ eq
      · intro i j; by_cases e : i=j
        · subst j; exact G.loopless.irrefl _
        · exact P.induced _ _ e _ _
      · exact fun i => P.edges i _
      · exact fun i => P.res i _
      · intro i; have h := P.hits l i
        cases e : t i <;> simpa [mate,e,or_comm] using h
      · exact (spec l hl).1
      · intro z ne
        by_contra! no
        exact ne ((spec l hl).2 z no)
      · intro S hs
        apply P.clean S
        intro z
        obtain ⟨v,hv,hm⟩ := hs z
        exact ⟨v,hm,hv⟩
    rw [full]
    ext z
    simp only [Finset.mem_image,Finset.mem_univ,true_and]
    constructor
    · rintro ⟨i,rfl⟩
      exact ⟨finTwoEquiv i,by simp [row,mate,t]⟩
    · rintro ⟨i,rfl⟩
      exact ⟨finTwoEquiv.symm i,rfl⟩
  · intro l l' hl hl' eq
    have rows : pick l = pick l' := by
      funext i
      have h := congrFun eq (finTwoEquiv i)
      simpa [row] using h
    exact (spec l' hl').2 _ (rows ▸ (spec l hl).1)

private theorem exact_gain {V : Type*} [DecidableEq V] {s t : ℕ}
    (P : Bool → Bool → V) (Q : Fin s → Bool → V) (R : Fin t → Bool → V)
    (row : Bool → Bool) (cost : ℕ)
    (minCost : ∀ S : Finset V, (∀ i, ∃ k, P i k ∈ S) →
      (∀ i, ∃ k, Q i k ∈ S) → (∀ i, ∃ k, R i k ∈ S) → cost ≤ S.card)
    (hits : ∀ j, ∃ k, Q j k ∈ Finset.univ.image (fun i => P i (row i))) :
    s ≤ 2+s+t-cost := by
  let left := Finset.univ.image (fun i => P i (row i))
  let right := Finset.univ.image (fun j => R j false)
  have c := minCost (left ∪ right)
    (fun i => ⟨_, Finset.mem_union_left _ (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩)
    (fun j => by obtain ⟨k,h⟩ := hits j; exact ⟨k,Finset.mem_union_left _ h⟩)
    (fun j => ⟨false,Finset.mem_union_right _ (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩)
  have c1 := Finset.card_union_le left right
  have c2 : left.card ≤ 2 := by
    simpa [left] using Finset.card_image_le (s := (Finset.univ : Finset Bool)) (f := fun i => P i (row i))
  have c3 : right.card ≤ t := by
    simpa [right] using Finset.card_image_le (s := (Finset.univ : Finset (Fin t))) (f := fun j => R j false)
  omega

private theorem joint_threshold {L : Type*} [DecidableEq L] (B D bad : Finset L) (m s t gain n : ℕ)
    (dis : Disjoint B D) (cap : bad.card ≤ 2*(n-4))
    (left : ∀ l ∈ B, l ∉ bad → s ≤ gain) (right : ∀ l ∈ D, l ∉ bad → t ≤ gain)
    (enough : 2*(n-4) < (if m≤s then B.card else 0) + (if m≤t then D.card else 0)) : m ≤ gain := by
  classical
  let U := if m≤s then B else ∅
  let V := if m≤t then D else ∅
  apply shared_slot_gain U V bad m gain n
  · by_cases hs : m≤s <;> by_cases ht : m≤t <;> simp [U,V,hs,ht,dis]
  · exact cap
  · simpa [U,V,apply_ite Finset.card] using enough
  · intro l hl ok
    by_cases hs : m≤s
    · exact hs.trans (left _ (by simpa [U,hs] using hl) ok)
    · simp [U,hs] at hl
  · intro l hl ok
    by_cases ht : m≤t
    · exact ht.trans (right _ (by simpa [V,ht] using hl) ok)
    · simp [V,ht] at hl

private theorem tight_neighbor (P : Batch G C A W 2)
    {b' w' s : ℕ} {B : Fin b' → Clause n} {W' : Fin w' → Clause n}
    (Q : Batch G C B W' s) (block : Finset (Fin a ⊕ Fin w))
    (row : (Fin a ⊕ Fin w) → Bool → Bool) (inj : Function.Injective row)
    (leaf : ∀ l ∈ block, literals A W l =
      Finset.univ.image (fun i => P.pt (finTwoEquiv.symm i) (row l i)))
    (shared : ∀ l ∈ block, ∀ j, ∃ k, Q.pt j k ∈ literals A W l)
    (exclusive : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (hs : s=2) : block.card < 2 := by
  subst s
  let pa (v : Endpoint) := P.pt (finTwoEquiv.symm v.1) v.2
  let qb (v : Endpoint) := Q.pt (finTwoEquiv.symm v.1) v.2
  apply tight_shared_card G pa qb (literals A W) block row inj leaf
  · intro l hl j; exact shared l hl (finTwoEquiv.symm j)
  · intro i; exact P.edges _ false
  · intro k l; exact Q.sep _ _ (fun e => Bool.false_ne_true (finTwoEquiv.symm.injective e)) _ _
  · intro v w adj
    by_contra ne
    exact Q.induced _ _ (fun eq => ne (finTwoEquiv.symm.injective eq)) _ _ adj
  · intro i j k l hk hl
    by_cases e : k=l
    · subst l
      exact G.irrefl (by simpa only [hk,hl] using (show G.Adj (pa (i,false)) (pa (i,true)) from P.edges _ false))
    · have op : l = !k := by cases k <;> cases l <;> first | rfl | exact (e rfl).elim
      subst l
      apply exclusive (finTwoEquiv.symm i) (finTwoEquiv.symm j) false k
      change s(pa (i,false), pa (i,true)) = s(qb (j,k),qb (j,!k))
      rw [hk,hl]

theorem small_rule_of_batches {r s t b' d' w' z' : ℕ}
    {B : Fin b' → Clause n} {V : Fin w' → Clause n}
    {D : Fin d' → Clause n} {Z : Fin z' → Clause n}
    (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B V s) (R : Batch G C D Z t)
    (bblock dblock : Finset (Fin a ⊕ Fin w)) (dis : Disjoint bblock dblock)
    (bhit : ∀ l ∈ bblock, ∀ j, ∃ k, Q.pt j k ∈ literals A W l)
    (dhit : ∀ l ∈ dblock, ∀ j, ∃ k, R.pt j k ∈ literals A W l)
    (bex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (dex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(R.pt j l,R.pt j (!l)))
    (cost : ℕ) (minCost : ∀ S : Finset (Fin n), (∀ i, ∃ k, P.pt i k ∈ S) →
      (∀ i, ∃ k, Q.pt i k ∈ S) → (∀ i, ∃ k, R.pt i k ∈ S) → cost ≤ S.card) :
    smallRule (a+w) r bblock.card s dblock.card t (r+s+t-cost) := by
  intro hr
  subst r
  obtain ⟨bad,row,cap,leaf,unique⟩ := small_occurrences four P
  let pa i := P.pt (finTwoEquiv.symm i)
  have amin (S : Finset (Fin n)) (h : ∀ i, ∃ k, pa i k ∈ S) :
      ∀ i, ∃ k, P.pt i k ∈ S := fun i => by simpa [pa] using h (finTwoEquiv i)
  have left (l) (hl : l ∈ bblock) (ok : l ∉ bad) : s ≤ 2+s+t-cost := by
    apply exact_gain pa Q.pt R.pt (row l) cost (fun S aa => minCost S (amin S aa))
    intro j
    rw [← leaf l ok]
    exact bhit l hl j
  have right (l) (hl : l ∈ dblock) (ok : l ∉ bad) : t ≤ 2+s+t-cost := by
    have h := exact_gain pa R.pt Q.pt (row l) cost
      (fun S aa rr qq => minCost S (amin S aa) qq rr) (fun j => by
        rw [← leaf l ok]
        exact dhit l hl j)
    omega
  have gain m := joint_threshold bblock dblock bad m s t (2+s+t-cost) (a+w) dis cap left right
  have none (tight : a+w=4) : bad = ∅ := Finset.card_eq_zero.mp (by omega)
  refine ⟨gain 1,gain 2,?_,?_⟩
  · intro tight hs
    have h (l) : l ∉ bad := by simp [none tight]
    exact tight_neighbor P Q bblock row (fun {i j} eq => unique _ _ (h _) (h _) eq)
      (fun l _ => leaf l (h _)) bhit bex hs
  · intro tight ht
    have h (l) : l ∉ bad := by simp [none tight]
    exact tight_neighbor P R dblock row (fun {i j} eq => unique _ _ (h _) (h _) eq)
      (fun l _ => leaf l (h _)) dhit dex ht

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
