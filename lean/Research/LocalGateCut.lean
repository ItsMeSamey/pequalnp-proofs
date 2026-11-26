import Research.CircuitRewire

namespace LocalGateCut
open CircuitRewire

private theorem transfer {Z : Type*} (X : ℕ → Set Z) (g : Gate) (u v : Z)
    (hl : u ∈ X g.left → v ∈ X g.left) (hr : u ∈ X g.right → v ∈ X g.right) :
    u ∈ g.eval X → v ∈ g.eval X := by
  cases g with
  | mk op a b =>
    cases op with
    | join => exact Or.imp hl hr
    | meet => exact fun h => ⟨hl h.1,hr h.2⟩
    | copy => exact hl
    | zero => exact id

theorem cut_ordered {Z : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (ho : o < m+s) (ordered : ∀ k < s, (raw k).left < m+k ∧ (raw k).right < m+k)
    (sem : ∀ k < s, X (m+k) = (raw k).eval X) (L : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ L.card+1 ∧
      (∀ j∈S, j<m+s ∧ (j<m ∨ j-m∉L)) ∧
      ∀ u v, (∀ j∈S, u∈X j → v∈X j) → u∈X o → v∈X o := by
  have reach (k : ℕ) (hk : k ≤ s) (W : Finset ℕ)
      (good : ∀ w∈W, w<m+s ∧ (w<m+k ∨ w-m∉L)) :
      ∃ S : Finset ℕ, S.card ≤ W.card+(L ∩ Finset.range k).card ∧
        (∀ j∈S, j<m+s ∧ (j<m ∨ j-m∉L)) ∧
        ∀ u v, (∀ j∈S, u∈X j → v∈X j) → ∀ w∈W, u∈X w → v∈X w := by
    induction k generalizing W with
    | zero => exact ⟨W,by simp,by simpa using good,fun _ _ h => h⟩
    | succ k ih =>
      let z := m+k
      by_cases expand : z ∈ W ∧ k ∈ L
      · obtain ⟨inW,inL⟩ := expand
        let g := raw k
        let U := insert g.left (insert g.right (W.erase z))
        have n := ordered k (by omega)
        have hl : g.left < z := n.1
        have hr : g.right < z := n.2
        have step : ∀ w∈U, w<m+s ∧ (w<m+k ∨ w-m∉L) := by
          intro w hw
          rcases Finset.mem_insert.mp hw with e|hw
          · subst w; exact ⟨by dsimp [z] at hl; omega,Or.inl hl⟩
          rcases Finset.mem_insert.mp hw with e|hw
          · subst w; exact ⟨by dsimp [z] at hr; omega,Or.inl hr⟩
          obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hw
          obtain ⟨lim,lo|done'⟩ := good w mem
          · exact ⟨lim,Or.inl (by dsimp [z] at ne; omega)⟩
          · exact ⟨lim,Or.inr done'⟩
        obtain ⟨S,hS,valid,dep⟩ := ih (by omega) U step
        have countU : U.card ≤ W.card+1 := by
          have c₁ := Finset.card_insert_le g.left (insert g.right (W.erase z))
          have c₂ := Finset.card_insert_le g.right (W.erase z)
          rw [Finset.card_erase_of_mem inW] at c₂
          have pos := Finset.card_pos.mpr ⟨_,inW⟩
          dsimp [U]; omega
        have countL : (L ∩ Finset.range (k+1)).card = (L ∩ Finset.range k).card+1 := by
          have eq : L ∩ Finset.range (k+1) = insert k (L ∩ Finset.range k) := by
            ext j; rw [Finset.range_add_one]; simp only [Finset.mem_inter,Finset.mem_insert]
            constructor
            · rintro ⟨h,h'|h'⟩
              · exact Or.inl h'
              · exact Or.inr ⟨h,h'⟩
            · rintro (rfl|h)
              · exact ⟨inL,Or.inl rfl⟩
              · exact ⟨h.1,Or.inr h.2⟩
          rw [eq,Finset.card_insert_of_notMem (by simp)]
        refine ⟨S,by omega,valid,?_⟩
        intro u v agree w hw
        by_cases eq : w=z
        · subst w
          rw [show X z = g.eval X from sem k (by omega)]
          exact transfer X g u v (dep u v agree _ (by simp [U])) (dep u v agree _ (by simp [U]))
        · exact dep u v agree w (by simp [U,hw,eq])
      · have step : ∀ w∈W, w<m+s ∧ (w<m+k ∨ w-m∉L) := by
          intro w hw
          obtain ⟨lim,lo|done'⟩ := good w hw
          · by_cases eq : w=z
            · subst w
              have ne : k ∉ L := fun h => expand ⟨hw,h⟩
              exact ⟨lim,Or.inr (by simpa [z] using ne)⟩
            · exact ⟨lim,Or.inl (by dsimp [z] at eq; omega)⟩
          · exact ⟨lim,Or.inr done'⟩
        obtain ⟨S,hS,valid,dep⟩ := ih (by omega) W step
        have inc : L ∩ Finset.range k ⊆ L ∩ Finset.range (k+1) :=
          Finset.inter_subset_inter (by rfl) (Finset.range_mono (by omega))
        exact ⟨S,by have := Finset.card_le_card inc; omega,valid,dep⟩
  obtain ⟨S,len,valid,dep⟩ := reach s le_rfl {o} (by simpa using And.intro ho (Or.inl ho))
  have cap := Finset.card_le_card (Finset.inter_subset_left : L ∩ Finset.range s ⊆ L)
  simp only [Finset.card_singleton] at len
  exact ⟨S,by omega,valid,fun u v h => dep u v h o (by simp)⟩

theorem cut {Z : Type*} (m s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set Z)
    (ho : o < m+s) (norm : ∀ k < s, Normal (raw k) (m+k))
    (sem : ∀ k < s, X (m+k) = (raw k).eval X) (L : Finset ℕ) :
    ∃ S : Finset ℕ, S.card ≤ L.card+1 ∧
      (∀ j∈S, j<m+s ∧ (j<m ∨ j-m∉L)) ∧
      ∀ u v, (∀ j∈S, u∈X j → v∈X j) → u∈X o → v∈X o :=
  cut_ordered m s o raw X ho (fun k hk => ⟨(norm k hk).1,(norm k hk).2.1⟩) sem L

end LocalGateCut
