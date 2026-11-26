import Mathlib.Data.Fintype.Card

namespace AffinePigeonhole

def parity : List Bool → Bool
  | [] => false
  | b :: t => b ^^ parity t

def prefixTest (p : Bool) : List Bool → Prop
  | [] => True
  | b :: t => (b = true → p = false) ∧ prefixTest (p ^^ b) t

theorem prefixTest_iff (p : Bool) (s : List Bool) :
    prefixTest p s ↔ s.count true ≤ (if p then 0 else 1) := by
  induction s generalizing p with
  | nil => simp [prefixTest]
  | cons b t ih =>
    cases p <;> cases b <;> simp [prefixTest, ih]

theorem zero_prefix_iff (s : List Bool) :
    prefixTest false s ↔ s.count true ≤ 1 := prefixTest_iff false s

theorem prefixTest_observations (p : Bool) (s : List Bool) :
    prefixTest p s ↔ ∀ a c, s = a ++ true :: c → (p ^^ parity a) = false := by
  induction s generalizing p with
  | nil => simp [prefixTest]
  | cons b t ih =>
    constructor
    · rintro ⟨hb,ht⟩ a c e
      cases a with
      | nil =>
        simp only [List.nil_append, List.cons.injEq] at e
        simpa [parity] using hb e.1
      | cons q a =>
        have eqs : b = q ∧ t = a ++ true :: c := List.cons.inj e
        rw [← eqs.1]
        simpa [parity, Bool.xor_assoc] using (ih _).mp ht a c eqs.2
    · intro h
      constructor
      · rintro rfl
        simpa [parity] using h [] t rfl
      · apply (ih _).mpr
        intro a c he
        simpa [parity, Bool.xor_assoc] using h (b :: a) c (by simp [he])

theorem odd_has_selected (s : List α) (f : α → Bool)
    (h : parity (s.map f) = true) : ∃ x ∈ s, f x = true := by
  induction s with
  | nil => contradiction
  | cons a t ih =>
    cases ha : f a with
    | true => exact ⟨a, List.mem_cons_self, ha⟩
    | false =>
      obtain ⟨x,hx,hf⟩ := ih (by simpa [parity, ha] using h)
      exact ⟨x,List.mem_cons_of_mem _ hx,hf⟩

theorem zero_count_absent (s : List α) (f : α → Bool)
    (h : (s.map f).count true = 0) {x} (hx : x ∈ s) : f x ≠ true := by
  intro e
  have hm : true ∈ s.map f := List.mem_map.mpr ⟨x,hx,e⟩
  exact (List.count_eq_zero.mp h) hm

theorem selected_unique (s : List α) (f : α → Bool)
    (h : (s.map f).count true ≤ 1) {x y} (hx : x ∈ s) (hy : y ∈ s)
    (fx : f x = true) (fy : f y = true) : x = y := by
  induction s with
  | nil => contradiction
  | cons a t ih =>
    cases ha : f a with
    | false =>
      rcases List.mem_cons.mp hx with rfl | hx
      · simp_all
      rcases List.mem_cons.mp hy with rfl | hy
      · simp_all
      exact ih (by simpa [ha] using h) hx hy
    | true =>
      have ht : (t.map f).count true = 0 := by simpa [ha] using h
      rcases List.mem_cons.mp hx with rfl | hx
      · rcases List.mem_cons.mp hy with rfl | hy
        · rfl
        · exact False.elim (zero_count_absent t f ht hy fy)
      · exact False.elim (zero_count_absent t f ht hx fx)

/-- Sparse adjacency lists can have arbitrary orders. A selected row edge
must be listed in its column; unselected nonedges need no constraints. -/
theorem no_guarded_assignment {P H : Type*} [Fintype P] [Fintype H]
    (rows : P → List H) (cols : H → List P) (f : P → H → Bool)
    (incidence : ∀ p h, h ∈ rows p → f p h = true → p ∈ cols h)
    (odd : ∀ p, parity ((rows p).map (f p)) = true)
    (guards : ∀ h, prefixTest false ((cols h).map (fun p => f p h)))
    (size : Fintype.card H < Fintype.card P) : False := by
  classical
  have existsHole := fun p => odd_has_selected (rows p) (f p) (odd p)
  let hole := fun p => (existsHole p).choose
  have edge (p) : hole p ∈ rows p ∧ f p (hole p) = true := (existsHole p).choose_spec
  have inj : Function.Injective hole := by
    intro p q e
    have hp := edge p
    rw [e] at hp
    have hq := edge q
    exact selected_unique (cols (hole q)) (fun r => f r (hole q))
      ((zero_prefix_iff _).mp (guards _))
      (incidence _ _ hp.1 hp.2) (incidence _ _ hq.1 hq.2) hp.2 hq.2
  exact (Nat.not_le_of_lt size) (Fintype.card_le_of_injective hole inj)

end AffinePigeonhole
