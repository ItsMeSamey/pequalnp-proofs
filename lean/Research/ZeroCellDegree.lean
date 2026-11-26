import Research.MissingCellRigidity

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem zeroCell_degree_falseLive {n m : ℕ} (A : Fin n → Fin m → Bool)
    (i : Fin n) (j : Fin m) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents A C) (hz : A i j = false) :
    (Finset.univ.filter (fun u => A u j)).card + (Finset.univ.filter (fun v => A i v)).card ≤
      (falseLive C.gates (oneEach i j) C.output).card := by
  classical
  let S := falseLive C.gates (oneEach i j) C.output
  let B (u : Fin n) (v : Fin m) := decide (∃ k ∈ S, (oneEach i j).getD k false = false ∧
    (oneEach u v).getD k false = true)
  have base : B i j = false := by simp [B]
  have pos (u : Fin n) (v : Fin m) (hp : A u v = true) : B u v = true := by
    apply decide_eq_true
    by_contra missed
    have h := falseLive_semantic C (oneEach i j) (oneEach u v) hm (by simp [oneEach]) (by
      intro k hk hfk
      cases he : (oneEach u v).getD k false with
      | false => rfl
      | true => exact False.elim (missed ⟨k,hk,hfk,he⟩)) ((hr i j).trans hz)
    rw [hr u v, hp] at h
    contradiction
  apply mixed_support B S
  · intro u hu
    exact ⟨j,i,pos u j (Finset.mem_filter.mp hu).2,base⟩
  · intro v hv
    exact ⟨i,j,pos i v (Finset.mem_filter.mp hv).2,base⟩
  · intro u v w z inc huv
    obtain ⟨k,hk,hf,ht⟩ := of_decide_eq_true huv
    exact decide_eq_true ⟨k,hk,hf,inc k hk ht⟩

theorem zeroCell_degree_or_count {n m : ℕ} (A : Fin n → Fin m → Bool)
    (i : Fin n) (j : Fin m) (C : Circuit) (hm : Monotone2 C)
    (hr : Represents A C) (hz : A i j = false) :
    (Finset.univ.filter (fun u => A u j)).card + (Finset.univ.filter (fun v => A i v)).card ≤
      (C.gates.filter isOrGate).length + 1 :=
  (zeroCell_degree_falseLive A i j C hm hr hz).trans
    (falseLive_card _ _ _ (fun g hg => (hm g hg).2))

theorem crown_twelve_or_count (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) :
    21 ≤ (C.gates.filter isOrGate).length := by
  have h := zeroCell_degree_or_count (fun u v : Fin 12 => decide (u ≠ v)) 0 0 C hm hr (by decide)
  have hcol : (Finset.univ.filter (fun u : Fin 12 => decide (u ≠ 0))).card = 11 := by decide
  have hrow : (Finset.univ.filter (fun v : Fin 12 => decide (0 ≠ v))).card = 11 := by decide
  rw [hcol,hrow] at h
  omega

end PEqualNP.Research.MissingCell
