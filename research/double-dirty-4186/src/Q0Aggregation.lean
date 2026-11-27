import Graph18272Bridge

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.S4183.S98

theorem clean_or_count {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : TopForm G C) :
    (orT G C).card + 1 = (tops G C).card :=
  (main_real n G C edge least form).2.2

theorem graph_iff_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (x : Fin n → Bool) :
    graphFun G ∅ x = true ↔ ∃ t ∈ tops G C, gateVal n C t x = true := by
  have hf : ∀ y : Fin n → Bool, C.eval (List.ofFn y) = graphFun G ∅ y := fun y => congrFun least.2.1 y
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun D hD agree =>
    least.2.2 D (IsAO2_of_AO n D hD) (funext fun y => (agree y).trans (hf y))⟩
  have hT : ∃ y : Fin n → Bool, C.eval (List.ofFn y) = true := by
    obtain ⟨y, hy⟩ := gf_true n G edge
    exact ⟨y, (hf y).trans hy⟩
  have hV : ∀ u : Fin n, ∃ y : Fin n → Bool, y u = true ∧ C.eval (List.ofFn y) = false := by
    intro u
    obtain ⟨y, h1, h2⟩ := gf_var n G u
    exact ⟨y, h1, (hf y).trans h2⟩
  have desc (j : ℕ) : j < C.gates.length → Bel n C j → W n C x (n+j) = true →
      ∃ t ∈ tops G C, gateVal n C t x = true := by
    induction j using Nat.strong_induction_on with
    | _ j ih =>
      intro hj hb hx
      rcases (hL.1 j hj).1 with ha | ho
      · refine ⟨j, ?_, hx⟩
        simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range]
        exact ⟨hj, ha, fun y hy => (hf y).symm.trans (hb y hy)⟩
      · obtain ⟨a,b,hin,har,hbr,_,hba,hbb⟩ := or_children n C hL hV j hj ho hb
        rw [W_or n C x j hj ho _ _ hin (by omega) (by omega)] at hx
        rcases Bool.or_eq_true_iff.mp hx with h | h
        · exact ih a har (by omega) hba h
        · exact ih b hbr (by omega) hbb h
  constructor
  · intro hx
    obtain ⟨hmin,hout⟩ := least_out n C hL hT hV
    have hidx : n + (C.output - n) = C.output := by omega
    apply desc (C.output - n) (by omega)
    · intro y hy
      rw [hidx] at hy
      exact hy
    · rw [hidx]
      exact (hf x).trans hx
  · rintro ⟨t, ht, hx⟩
    simp only [tops, gatesWhere, Finset.mem_filter, Finset.mem_range] at ht
    exact ht.2.2 x hx

theorem rebuild_or (n : ℕ) (C : Circuit) (first : ℕ) (rest : List ℕ)
    (hC : AO n C) (hf : first < n + C.gates.length)
    (hr : ∀ w ∈ rest, w < n + C.gates.length) :
    ∃ D : Circuit, AO n D ∧ D.gates.length = C.gates.length + rest.length ∧
      D.output < n + D.gates.length ∧
      (∀ x : Fin n → Bool, ∀ i < n + C.gates.length, W n D x i = W n C x i) ∧
      (∀ x : Fin n → Bool, D.eval (List.ofFn x) = true ↔
        ∃ w ∈ first :: rest, W n C x w = true) := by
  induction rest generalizing C first with
  | nil =>
    refine ⟨⟨C.gates, first⟩, hC, by simp, hf, fun _ _ _ => rfl, ?_⟩
    intro x
    simp only [List.mem_singleton, exists_eq_left]
    rfl
  | cons b bs ih =>
    let C' := appOr n C first b
    have hb := hr b (by simp)
    have hlen : C'.gates.length = C.gates.length + 1 := by simp [C', appOr]
    have hop : C'.output = n + C.gates.length := rfl
    obtain ⟨D,hD,hlenD,houtD,holdD,heD⟩ := ih C' C'.output
      (appOr_AO n C first b hC hf hb) (by rw [hop, hlen]; omega)
      (fun w hw => by have := hr w (by simp [hw]); rw [hlen]; omega)
    refine ⟨D,hD,by rw [hlenD, hlen, List.length_cons]; omega, houtD, ?_, ?_⟩
    · intro x i hi
      exact (holdD x i (by rw [hlen]; omega)).trans (appOr_W_lt n C first b x i hi)
    · intro x
      rw [heD]
      have he : W n C' x C'.output = (W n C x first || W n C x b) :=
        appOr_eval n C first b x hf hb
      constructor
      · rintro ⟨w, hw, hv⟩
        rcases List.mem_cons.mp hw with hw | hw
        · subst w
          rw [he] at hv
          rcases Bool.or_eq_true_iff.mp hv with h | h
          · exact ⟨first, by simp, h⟩
          · exact ⟨b, by simp, h⟩
        · exact ⟨w, by simp [hw], (appOr_W_lt n C first b x w (hr w (by simp [hw]))).symm.trans hv⟩
      · rintro ⟨w, hw, hv⟩
        rcases List.mem_cons.mp hw with hw | hw
        · subst w
          exact ⟨C'.output, by simp, by rw [he, hv]; rfl⟩
        · rcases List.mem_cons.mp hw with hw | hw
          · subst w
            exact ⟨C'.output, by simp, by rw [he, hv]; simp⟩
          · exact ⟨w, by simp [hw], (appOr_W_lt n C first b x w (hr w (by simp [hw]))).trans hv⟩

end PEqualNP.Outside.L_meta_4186_aux.Q0
