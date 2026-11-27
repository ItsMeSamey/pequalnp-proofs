import Enriched30PivotFacts

namespace Enriched30Pivot

private theorem essential_checked : ∀ j : Fin 30, j.val ∈ mandatory → essentialCheck j = true := by
  intro j hj
  by_cases h0 : j.val = 0
  · have he : j = (0 : Fin 30) := Fin.ext h0
    subst j
    exact essentialOK0
  by_cases h1 : j.val = 1
  · have he : j = (1 : Fin 30) := Fin.ext h1
    subst j
    exact essentialOK1
  by_cases h2 : j.val = 2
  · have he : j = (2 : Fin 30) := Fin.ext h2
    subst j
    exact essentialOK2
  by_cases h3 : j.val = 3
  · have he : j = (3 : Fin 30) := Fin.ext h3
    subst j
    exact False.elim ((by decide : ¬ (3 : Nat) ∈ mandatory) hj)
  by_cases h4 : j.val = 4
  · have he : j = (4 : Fin 30) := Fin.ext h4
    subst j
    exact essentialOK4
  by_cases h5 : j.val = 5
  · have he : j = (5 : Fin 30) := Fin.ext h5
    subst j
    exact essentialOK5
  by_cases h6 : j.val = 6
  · have he : j = (6 : Fin 30) := Fin.ext h6
    subst j
    exact essentialOK6
  by_cases h7 : j.val = 7
  · have he : j = (7 : Fin 30) := Fin.ext h7
    subst j
    exact essentialOK7
  by_cases h8 : j.val = 8
  · have he : j = (8 : Fin 30) := Fin.ext h8
    subst j
    exact essentialOK8
  by_cases h9 : j.val = 9
  · have he : j = (9 : Fin 30) := Fin.ext h9
    subst j
    exact essentialOK9
  by_cases h10 : j.val = 10
  · have he : j = (10 : Fin 30) := Fin.ext h10
    subst j
    exact False.elim ((by decide : ¬ (10 : Nat) ∈ mandatory) hj)
  by_cases h11 : j.val = 11
  · have he : j = (11 : Fin 30) := Fin.ext h11
    subst j
    exact essentialOK11
  by_cases h12 : j.val = 12
  · have he : j = (12 : Fin 30) := Fin.ext h12
    subst j
    exact essentialOK12
  by_cases h13 : j.val = 13
  · have he : j = (13 : Fin 30) := Fin.ext h13
    subst j
    exact essentialOK13
  by_cases h14 : j.val = 14
  · have he : j = (14 : Fin 30) := Fin.ext h14
    subst j
    exact essentialOK14
  by_cases h15 : j.val = 15
  · have he : j = (15 : Fin 30) := Fin.ext h15
    subst j
    exact essentialOK15
  by_cases h16 : j.val = 16
  · have he : j = (16 : Fin 30) := Fin.ext h16
    subst j
    exact essentialOK16
  by_cases h17 : j.val = 17
  · have he : j = (17 : Fin 30) := Fin.ext h17
    subst j
    exact essentialOK17
  by_cases h18 : j.val = 18
  · have he : j = (18 : Fin 30) := Fin.ext h18
    subst j
    exact essentialOK18
  by_cases h19 : j.val = 19
  · have he : j = (19 : Fin 30) := Fin.ext h19
    subst j
    exact essentialOK19
  by_cases h20 : j.val = 20
  · have he : j = (20 : Fin 30) := Fin.ext h20
    subst j
    exact essentialOK20
  by_cases h21 : j.val = 21
  · have he : j = (21 : Fin 30) := Fin.ext h21
    subst j
    exact essentialOK21
  by_cases h22 : j.val = 22
  · have he : j = (22 : Fin 30) := Fin.ext h22
    subst j
    exact essentialOK22
  by_cases h23 : j.val = 23
  · have he : j = (23 : Fin 30) := Fin.ext h23
    subst j
    exact essentialOK23
  by_cases h24 : j.val = 24
  · have he : j = (24 : Fin 30) := Fin.ext h24
    subst j
    exact essentialOK24
  by_cases h25 : j.val = 25
  · have he : j = (25 : Fin 30) := Fin.ext h25
    subst j
    exact essentialOK25
  by_cases h26 : j.val = 26
  · have he : j = (26 : Fin 30) := Fin.ext h26
    subst j
    exact essentialOK26
  by_cases h27 : j.val = 27
  · have he : j = (27 : Fin 30) := Fin.ext h27
    subst j
    exact essentialOK27
  by_cases h28 : j.val = 28
  · have he : j = (28 : Fin 30) := Fin.ext h28
    subst j
    exact essentialOK28
  by_cases h29 : j.val = 29
  · have he : j = (29 : Fin 30) := Fin.ext h29
    subst j
    exact essentialOK29
  omega

private theorem binate_checked : ∀ j : Fin 30, j.val ∈ binate → binateCheck j = true := by
  intro j hj
  by_cases h0 : j.val = 0
  · have he : j = (0 : Fin 30) := Fin.ext h0
    subst j
    exact False.elim ((by decide : ¬ (0 : Nat) ∈ binate) hj)
  by_cases h1 : j.val = 1
  · have he : j = (1 : Fin 30) := Fin.ext h1
    subst j
    exact False.elim ((by decide : ¬ (1 : Nat) ∈ binate) hj)
  by_cases h2 : j.val = 2
  · have he : j = (2 : Fin 30) := Fin.ext h2
    subst j
    exact binateOK2
  by_cases h3 : j.val = 3
  · have he : j = (3 : Fin 30) := Fin.ext h3
    subst j
    exact False.elim ((by decide : ¬ (3 : Nat) ∈ binate) hj)
  by_cases h4 : j.val = 4
  · have he : j = (4 : Fin 30) := Fin.ext h4
    subst j
    exact binateOK4
  by_cases h5 : j.val = 5
  · have he : j = (5 : Fin 30) := Fin.ext h5
    subst j
    exact False.elim ((by decide : ¬ (5 : Nat) ∈ binate) hj)
  by_cases h6 : j.val = 6
  · have he : j = (6 : Fin 30) := Fin.ext h6
    subst j
    exact False.elim ((by decide : ¬ (6 : Nat) ∈ binate) hj)
  by_cases h7 : j.val = 7
  · have he : j = (7 : Fin 30) := Fin.ext h7
    subst j
    exact binateOK7
  by_cases h8 : j.val = 8
  · have he : j = (8 : Fin 30) := Fin.ext h8
    subst j
    exact binateOK8
  by_cases h9 : j.val = 9
  · have he : j = (9 : Fin 30) := Fin.ext h9
    subst j
    exact binateOK9
  by_cases h10 : j.val = 10
  · have he : j = (10 : Fin 30) := Fin.ext h10
    subst j
    exact False.elim ((by decide : ¬ (10 : Nat) ∈ binate) hj)
  by_cases h11 : j.val = 11
  · have he : j = (11 : Fin 30) := Fin.ext h11
    subst j
    exact False.elim ((by decide : ¬ (11 : Nat) ∈ binate) hj)
  by_cases h12 : j.val = 12
  · have he : j = (12 : Fin 30) := Fin.ext h12
    subst j
    exact False.elim ((by decide : ¬ (12 : Nat) ∈ binate) hj)
  by_cases h13 : j.val = 13
  · have he : j = (13 : Fin 30) := Fin.ext h13
    subst j
    exact False.elim ((by decide : ¬ (13 : Nat) ∈ binate) hj)
  by_cases h14 : j.val = 14
  · have he : j = (14 : Fin 30) := Fin.ext h14
    subst j
    exact binateOK14
  by_cases h15 : j.val = 15
  · have he : j = (15 : Fin 30) := Fin.ext h15
    subst j
    exact False.elim ((by decide : ¬ (15 : Nat) ∈ binate) hj)
  by_cases h16 : j.val = 16
  · have he : j = (16 : Fin 30) := Fin.ext h16
    subst j
    exact binateOK16
  by_cases h17 : j.val = 17
  · have he : j = (17 : Fin 30) := Fin.ext h17
    subst j
    exact False.elim ((by decide : ¬ (17 : Nat) ∈ binate) hj)
  by_cases h18 : j.val = 18
  · have he : j = (18 : Fin 30) := Fin.ext h18
    subst j
    exact False.elim ((by decide : ¬ (18 : Nat) ∈ binate) hj)
  by_cases h19 : j.val = 19
  · have he : j = (19 : Fin 30) := Fin.ext h19
    subst j
    exact False.elim ((by decide : ¬ (19 : Nat) ∈ binate) hj)
  by_cases h20 : j.val = 20
  · have he : j = (20 : Fin 30) := Fin.ext h20
    subst j
    exact binateOK20
  by_cases h21 : j.val = 21
  · have he : j = (21 : Fin 30) := Fin.ext h21
    subst j
    exact False.elim ((by decide : ¬ (21 : Nat) ∈ binate) hj)
  by_cases h22 : j.val = 22
  · have he : j = (22 : Fin 30) := Fin.ext h22
    subst j
    exact binateOK22
  by_cases h23 : j.val = 23
  · have he : j = (23 : Fin 30) := Fin.ext h23
    subst j
    exact False.elim ((by decide : ¬ (23 : Nat) ∈ binate) hj)
  by_cases h24 : j.val = 24
  · have he : j = (24 : Fin 30) := Fin.ext h24
    subst j
    exact False.elim ((by decide : ¬ (24 : Nat) ∈ binate) hj)
  by_cases h25 : j.val = 25
  · have he : j = (25 : Fin 30) := Fin.ext h25
    subst j
    exact binateOK25
  by_cases h26 : j.val = 26
  · have he : j = (26 : Fin 30) := Fin.ext h26
    subst j
    exact False.elim ((by decide : ¬ (26 : Nat) ∈ binate) hj)
  by_cases h27 : j.val = 27
  · have he : j = (27 : Fin 30) := Fin.ext h27
    subst j
    exact False.elim ((by decide : ¬ (27 : Nat) ∈ binate) hj)
  by_cases h28 : j.val = 28
  · have he : j = (28 : Fin 30) := Fin.ext h28
    subst j
    exact binateOK28
  by_cases h29 : j.val = 29
  · have he : j = (29 : Fin 30) := Fin.ext h29
    subst j
    exact False.elim ((by decide : ¬ (29 : Nat) ∈ binate) hj)
  omega

theorem mandatory_pivot (j : Nat) (hj : j ∈ mandatory) :
    ∃ a b : Cell, label a ≠ label b ∧ (bits a).getD j false = false ∧
      (bits b).getD j false = true ∧ ∀ k : Nat, k ≠ j →
        (bits a).getD k false = (bits b).getD k false := by
  have h := essential_checked ⟨j,mandatory_lt hj⟩ hj
  change ((label (essentialPair j).1 != label (essentialPair j).2) &&
    edgeCode j (essentialPair j).1 (essentialPair j).2) = true at h
  obtain ⟨a,b⟩ := Bool.and_eq_true_iff.mp h
  exact ⟨_,_, by simpa using a, edge_sound b⟩

theorem binate_pivot (j : Nat) (hj : j ∈ binate) :
    (∃ a b : Cell, label a = false ∧ label b = true ∧ Edge j a b) ∧
    (∃ a b : Cell, label a = true ∧ label b = false ∧ Edge j a b) := by
  have lt : j < 30 := Finset.mem_range.mp (Finset.mem_filter.mp hj).1
  have h := binate_checked ⟨j,lt⟩ hj
  simp only [binateCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨r0,r1⟩,f0⟩,f1⟩,re,fe⟩ := h
  exact ⟨⟨_,_,r0,r1,edge_sound re⟩,⟨_,_,f0,f1,edge_sound fe⟩⟩

theorem donor89_rise :
    ∃ a b : Cell, label a = false ∧ label b = true ∧ Edge 2 a b :=
  (binate_pivot 2 (by decide)).1
theorem donor89_fall :
    ∃ a b : Cell, label a = true ∧ label b = false ∧ Edge 2 a b :=
  (binate_pivot 2 (by decide)).2

end Enriched30Pivot
