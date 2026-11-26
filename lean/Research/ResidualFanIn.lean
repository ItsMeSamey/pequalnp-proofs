import Research.FirstGate
import Research.CircuitRewire

namespace ResidualFanIn
open FirstGate

theorem lower {Z : Type*} (m s : ℕ) (X : ℕ → Set Z) (o : ℕ) (ho : o < m+s)
    (steps : ∀ g < s, ∃ a < m+g, ∃ b < m+g, Law (X a) (X b) (X (m+g)))
    (deleted : Finset ℕ) (hdel : deleted ⊆ Finset.range m) (large : 2 ≤ m-deleted.card)
    (essential : ∀ i < m, i ∉ deleted → Essential m X o i)
    (dist : ∀ a < m, a ∉ deleted → ∀ b < m, b ∉ deleted → a ≠ b → Distinguishes m X o a b) :
    m ≤ s+deleted.card := by
  let live := Finset.range m \ deleted
  have lc : live.card + deleted.card = m := by
    simpa [live] using Finset.card_sdiff_add_card_eq_card hdel
  by_contra! small
  cases s with
  | zero =>
    have hi : o < m := by omega
    obtain ⟨i,alive,ne⟩ := Finset.exists_mem_ne (show 1 < live.card by omega) o
    obtain ⟨inRange,undeleted⟩ := Finset.mem_sdiff.mp alive
    obtain ⟨u,hu,v,hv,h⟩ := essential i (Finset.mem_range.mp inRange) undeleted
    exact hv (h o hi ne.symm hu)
  | succ s =>
    obtain ⟨S,hS,c,dep⟩ := IncidenceBound.support (m+1) s X (by
      intro k hk
      simpa [Nat.add_assoc,Nat.add_left_comm,Nat.add_comm,Law] using steps (k+1) (by omega)) o (by omega)
    let T := S.erase m
    have below (t : ℕ) (ht : t ∈ T) : t < m := by
      obtain ⟨ne,inS⟩ := Finset.mem_erase.mp ht
      have := Finset.mem_range.mp (hS inS)
      omega
    have witness (a : ℕ) (ha : a < m) (alive : a ∉ deleted) (absent : a ∉ T)
        (unchanged : ∀ u v : Z, (∀ t < m, t ≠ a → u ∈ X t → v ∈ X t) →
          m ∈ S → u ∈ X m → v ∈ X m) : False := by
      obtain ⟨u,hu,v,hv,h⟩ := essential a ha alive
      apply hv (dep u v ?_ hu)
      intro t ht
      by_cases eq : t = m
      · subst t; exact unchanged u v h ht
      · have mem := Finset.mem_erase.mpr ⟨eq,ht⟩
        exact h t (below t mem) (fun e => absent (e ▸ mem))
    let D := live \ T
    have survivor (i : ℕ) (hi : i ∈ D) : i ∈ live := (Finset.mem_sdiff.mp hi).1
    have miss (i : ℕ) (hi : i ∈ D) : i < m ∧ i ∉ T :=
      ⟨Finset.mem_range.mp (Finset.mem_sdiff.mp (survivor i hi)).1,(Finset.mem_sdiff.mp hi).2⟩
    have alive (i : ℕ) (hi : i ∈ D) : i ∉ deleted :=
      (Finset.mem_sdiff.mp (survivor i hi)).2
    have diff : live.card ≤ D.card + T.card := Finset.card_le_card_sdiff_add_card
    by_cases use : m ∈ S
    · have size : T.card = S.card - 1 := Finset.card_erase_of_mem use
      have sc := Finset.card_pos.mpr ⟨_,use⟩
      obtain ⟨i,hi,j,hj,ij⟩ := Finset.one_lt_card.mp (show 1 < D.card by omega)
      obtain ⟨a,ha,b,hb,law⟩ := steps 0 (by omega)
      simp only [Nat.add_zero] at ha hb law
      have incident (k : ℕ) (hk : k ∈ D) : k = a ∨ k = b := by
        by_contra! hn
        apply witness k (miss k hk).1 (alive k hk) (miss k hk).2
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
      have aa : a ∉ deleted := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact alive _ hi | exact alive _ hj | contradiction
      have bb : b ∉ deleted := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact alive _ hi | exact alive _ hj | contradiction
      have haD : a ∉ T := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact (miss _ hi).2 | exact (miss _ hj).2 | contradiction
      have hbD : b ∉ T := by
        rcases ei with rfl|rfl <;> rcases ej with rfl|rfl <;> first | exact (miss _ hi).2 | exact (miss _ hj).2 | contradiction
      have ab : a ≠ b := by omega
      rcases law with union|copy|empty|inter
      · obtain ⟨u,hu,v,hv,pa,pb,h⟩ := dist a ha aa b hb bb ab
        apply hv (dep u v ?_ hu)
        intro k hk
        by_cases eq : k = m
        · subst k; rw [union]; exact fun h => h.elim (fun a => Or.inr (pa a)) (fun b => Or.inl (pb b))
        · have mem := Finset.mem_erase.mpr ⟨eq,hk⟩
          exact h k (below k mem) (fun e => haD (e ▸ mem)) (fun e => hbD (e ▸ mem))
      · apply witness b hb bb hbD
        intro u v h _; rw [copy]; exact h a ha ab
      · apply witness b hb bb hbD
        intro u v h _; rw [empty]; exact id
      · obtain ⟨u,hu,v,hv,pa,pb,h⟩ := dist a ha aa b hb bb ab
        apply hv (dep u v ?_ hu)
        intro k hk
        by_cases eq : k = m
        · subst k; rw [inter]; exact fun h => ⟨pb h.2,pa h.1⟩
        · have mem := Finset.mem_erase.mpr ⟨eq,hk⟩
          exact h k (below k mem) (fun e => haD (e ▸ mem)) (fun e => hbD (e ▸ mem))
    · have e : T = S := Finset.erase_eq_of_notMem use
      rw [e] at diff
      obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0 < D.card by omega)
      exact witness i (miss i hi).1 (alive i hi) (miss i hi).2 (fun _ _ _ hm => False.elim (use hm))

theorem internal {Z : Type*} (m o : ℕ) (X : ℕ → Set Z)
    (D : Finset ℕ) (hD : D ⊆ Finset.range m) (large : 2 ≤ m-D.card)
    (essential : ∀ i < m, i ∉ D → Essential m X o i) : m ≤ o := by
  by_contra! low
  let live := Finset.range m \ D
  have c : live.card + D.card = m := by
    simpa [live] using Finset.card_sdiff_add_card_eq_card hD
  obtain ⟨i,hi,ne⟩ := Finset.exists_mem_ne (show 1 < live.card by omega) o
  obtain ⟨inRange,alive⟩ := Finset.mem_sdiff.mp hi
  obtain ⟨u,hu,v,hv,h⟩ := essential i (Finset.mem_range.mp inRange) alive
  exact hv (h o low ne.symm hu)

theorem normalized {Z : Type*} (m s o : ℕ) (raw : ℕ → CircuitRewire.Gate) (X : ℕ → Set Z)
    (ho : o < m+s) (norm : ∀ k < s, CircuitRewire.Normal (raw k) (m+k))
    (sem : ∀ k < s, X (m+k) = (raw k).eval X)
    (D : Finset ℕ) (hD : D ⊆ Finset.range m) (large : 2 ≤ m-D.card)
    (essential : ∀ i < m, i ∉ D → Essential m X o i)
    (dist : ∀ a < m, a ∉ D → ∀ b < m, b ∉ D → a ≠ b → Distinguishes m X o a b) :
    m ≤ s+D.card := by
  apply lower m s X o ho _ D hD large essential dist
  intro k hk
  obtain ⟨left,right,_,op⟩ := norm k hk
  refine ⟨_,left,_,right,?_⟩
  rw [sem k hk]
  rcases op with join|meet
  · exact Or.inl (by simp [CircuitRewire.Gate.eval,join,CircuitRewire.Op.eval])
  · exact Or.inr (Or.inr (Or.inr (by simp [CircuitRewire.Gate.eval,meet,CircuitRewire.Op.eval])))

end ResidualFanIn
