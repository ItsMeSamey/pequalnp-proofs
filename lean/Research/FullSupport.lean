import Research.MissingCellRigidity

open PEqualNP.Research.MissingCell PEqualNP.Represents

theorem PEqualNP.Research.MissingCell.fullSupportLowerBound : ∀ (n m s : ℕ) (A : Fin n → Fin m → Bool), 2 ≤ n → 2 ≤ m →
  (∀ a : Fin n, ∃ b : Fin n, b ≠ a ∧ ∃ v : Fin m, A a v = true ∧ A b v = false) →
  (∀ v : Fin m, ∃ w : Fin m, w ≠ v ∧ ∃ a : Fin n, A a v = true ∧ A a w = false) →
  PEqualNP.Represents.RepSizeAtMost A s → n + m - 1 ≤ s := by
  intro n m s A _ _ rows cols bound
  obtain ⟨D, hm, hs, hr⟩ := bound
  let S := live D.gates (n+m) D.output
  have h := mixed_support A S Finset.univ Finset.univ
    (by
      intro u _
      obtain ⟨w, _, v, h₁, h₂⟩ := rows u
      exact ⟨v,w,h₁,h₂⟩)
    (by
      intro v _
      obtain ⟨w, _, u, h₁, h₂⟩ := cols v
      exact ⟨u,w,h₁,h₂⟩)
    (by
      intro u v w z h ht
      rw [←hr w z]
      apply eval_mono_live D (n+m) (oneEach u v) (oneEach w z) hm
        (by simp [oneEach]) (by simp [oneEach]) h
      simpa [hr u v] using ht)
  have hcard : n + m ≤ S.card := by simpa using h
  have hsize : S.card ≤ D.size + 1 :=
    live_card D.gates (n+m) D.output (fun g hg => (hm g hg).2)
  omega
