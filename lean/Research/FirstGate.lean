import Research.IncidenceBound

namespace FirstGate

def Law {Z : Type*} (A B C : Set Z) := C = A ∪ B ∨ C = A ∨ C = ∅ ∨ C = A ∩ B

def Essential {Z : Type*} (m : ℕ) (X : ℕ → Set Z) (o i : ℕ) :=
  ∃ u ∈ X o, ∃ v ∉ X o, ∀ t < m, t ≠ i → u ∈ X t → v ∈ X t

def Distinguishes {Z : Type*} (m : ℕ) (X : ℕ → Set Z) (o a b : ℕ) :=
  ∃ u ∈ X o, ∃ v ∉ X o, (u ∈ X a → v ∈ X b) ∧ (u ∈ X b → v ∈ X a) ∧
    ∀ t < m, t ≠ a → t ≠ b → u ∈ X t → v ∈ X t

theorem lower {Z : Type*} (m s : ℕ) (X : ℕ → Set Z) (o : ℕ) (ho : o < m+s)
    (steps : ∀ g < s, ∃ a < m+g, ∃ b < m+g, Law (X a) (X b) (X (m+g)))
    (large : 2 ≤ m) (essential : ∀ i < m, Essential m X o i)
    (dist : ∀ a < m, ∀ b < m, a ≠ b → Distinguishes m X o a b) : m ≤ s := by
  by_contra! small
  cases s with
  | zero =>
    have hi : o < m := by omega
    let i := if o = 0 then 1 else 0
    have him : i < m := by dsimp [i]; split <;> omega
    have ne : o ≠ i := by dsimp [i]; split <;> omega
    obtain ⟨u,hu,v,hv,h⟩ := essential i him
    exact hv (h o hi ne hu)
  | succ s =>
    obtain ⟨S,hS,c,dep⟩ := IncidenceBound.support (m+1) s X (by
      intro k hk
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Law] using steps (k+1) (by omega)) o (by omega)
    let T := S.erase m
    have below (t : ℕ) (ht : t ∈ T) : t < m := by
      obtain ⟨ne,inS⟩ := Finset.mem_erase.mp ht
      have := Finset.mem_range.mp (hS inS)
      omega
    have witness (a : ℕ) (ha : a < m) (absent : a ∉ T)
        (unchanged : ∀ u v : Z, (∀ t < m, t ≠ a → u ∈ X t → v ∈ X t) →
          m ∈ S → u ∈ X m → v ∈ X m) : False := by
      obtain ⟨u,hu,v,hv,h⟩ := essential a ha
      apply hv (dep u v ?_ hu)
      intro t ht
      by_cases eq : t = m
      · subst t; exact unchanged u v h ht
      · have mem := Finset.mem_erase.mpr ⟨eq,ht⟩
        exact h t (below t mem) (fun e => absent (e ▸ mem))
    let D := Finset.range m \ T
    have miss (i : ℕ) (hi : i ∈ D) : i < m ∧ i ∉ T :=
      ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    have diff := Finset.card_sdiff_add_card_eq_card (s := T) (t := Finset.range m)
      (fun t ht => Finset.mem_range.mpr (below t ht))
    change D.card + T.card = _ at diff
    rw [Finset.card_range] at diff
    by_cases use : m ∈ S
    · have size : T.card = S.card - 1 := Finset.card_erase_of_mem use
      have sc := Finset.card_pos.mpr ⟨_,use⟩
      obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (show 1 < D.card by omega)
      obtain ⟨a,ha,b,hb,law⟩ := steps 0 (by omega)
      simp only [Nat.add_zero] at ha hb law
      have incident (k : ℕ) (hk : k ∈ D) : k = a ∨ k = b := by
        by_contra! hn
        apply witness k (miss k hk).1 (miss k hk).2
        intro u v h _
        have pa := h a ha (Ne.symm hn.1)
        have pb := h b hb (Ne.symm hn.2)
        rcases law with union|copy|empty|inter
        · rw [union]; exact Or.imp pa pb
        · rw [copy]; exact pa
        · rw [empty]; exact id
        · rw [inter]; exact fun h => ⟨pa h.1,pb h.2⟩
      have ei := incident i hi
      have ej := incident j hj
      have haD : a ∉ T := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact (miss _ hi).2 | exact (miss _ hj).2 | contradiction
      have hbD : b ∉ T := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact (miss _ hi).2 | exact (miss _ hj).2 | contradiction
      have ab : a ≠ b := by omega
      rcases law with union|copy|empty|inter
      · obtain ⟨u,hu,v,hv,pa,pb,h⟩ := dist a ha b hb ab
        apply hv (dep u v ?_ hu)
        intro k hk
        by_cases eq : k = m
        · subst k; rw [union]; exact fun h => h.elim (fun a => Or.inr (pa a)) (fun b => Or.inl (pb b))
        · have mem := Finset.mem_erase.mpr ⟨eq,hk⟩
          exact h k (below k mem) (fun e => haD (e ▸ mem)) (fun e => hbD (e ▸ mem))
      · apply witness b hb hbD
        intro u v h _; rw [copy]; exact h a ha ab
      · apply witness b hb hbD
        intro u v h _; rw [empty]; exact id
      · obtain ⟨u,hu,v,hv,pa,pb,h⟩ := dist a ha b hb ab
        apply hv (dep u v ?_ hu)
        intro k hk
        by_cases eq : k = m
        · subst k; rw [inter]; exact fun h => ⟨pb h.2,pa h.1⟩
        · have mem := Finset.mem_erase.mpr ⟨eq,hk⟩
          exact h k (below k mem) (fun e => haD (e ▸ mem)) (fun e => hbD (e ▸ mem))
    · have e : T = S := Finset.erase_eq_of_notMem use
      rw [e] at diff
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
      exact witness i (miss i hi).1 (miss i hi).2 (fun _ _ _ hm => False.elim (use hm))

end FirstGate
