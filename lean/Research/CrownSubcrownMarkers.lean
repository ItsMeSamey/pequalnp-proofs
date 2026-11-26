import Research.CrownMarkerBound

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell
open scoped Classical

def restrictEnv {k n : ℕ} (e : Fin k ↪ Fin n) : Env k := fun p => oneEach (e p.1) (e p.2)

private theorem row_subset_charged {k n : ℕ} (e : Fin k ↪ Fin n) (a : Fin n) :
    Charged ∅ {p : Cell (Fin k) | a = e p.1} := by
  by_cases h : ∃ u, e u = a
  · obtain ⟨u,rfl⟩ := h
    refine Or.inl ⟨{u},∅,?_,fun hd => hd u rfl⟩
    ext p; simp [conjSupport]
  · exact Or.inr (fun p hp => False.elim (h ⟨p.1,hp.symm⟩))

private theorem col_subset_charged {k n : ℕ} (e : Fin k ↪ Fin n) (a : Fin n) :
    Charged ∅ {p : Cell (Fin k) | a = e p.2} := by
  by_cases h : ∃ u, e u = a
  · obtain ⟨u,rfl⟩ := h
    refine Or.inl ⟨∅,{u},?_,fun hd => hd u rfl⟩
    ext p; simp [conjSupport]
  · exact Or.inr (fun p hp => False.elim (h ⟨p.2,hp.symm⟩))

theorem subset_wire_charged {k n : ℕ} (e : Fin k ↪ Fin n) (i : ℕ) :
    Charged ∅ (wire (restrictEnv e) i) := by
  by_cases hi : i < n
  · have eq : wire (restrictEnv e) i = {p | (⟨i,hi⟩ : Fin n) = e p.1} := by
      ext p; simp [wire,restrictEnv,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hi]
    rw [eq]; exact row_subset_charged e _
  · by_cases hj : i-n < n
    · have eq : wire (restrictEnv e) i = {p | (⟨i-n,hj⟩ : Fin n) = e p.2} := by
        ext p; simp [wire,restrictEnv,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,
          Nat.le_of_not_gt hi,hj]
      rw [eq]; exact col_subset_charged e _
    · have eq : wire (restrictEnv e) i = ∅ := by
        ext p; simp [wire,restrictEnv,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_right,
          Nat.le_of_not_gt hi,hj]
      rw [eq]; exact initial_false

theorem subcrown_four_and {k n : ℕ} (e : Fin k ↪ Fin n) (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin n => decide (u ≠ v)) C)
    (budget : ∀ i, (trueOrFlags C.gates (oneEach (e i) (e i))).count true ≤ 1) :
    k*(k-1) ≤ 4*(C.gates.filter isAndGate).length := by
  classical
  let w := restrictEnv e
  let K : Set (WirePair (Fin k)) := {v | v.1 = v.2 ∧ MarkNormal ∅ v.2}
  have init (A : Support (Fin k)) (ch : Charged ∅ A) : A ∈ Actual K :=
    ⟨(supportCells A,supportCells A), ⟨rfl,initial_fin_normal A ch⟩,coe_supportCells A⟩
  have sep := orMarker_pairwise C.gates (fun i => oneEach (e i) (e i)) budget
  obtain ⟨J,N,tr,hw⟩ := marker_trace_eval C.gates w (n+n) 0 K ∅ MarkerTrace.start
    (init _ initial_false) (init _ initial_true) (fun i => init _ (subset_wire_charged e i))
    (fun p => by simp [w,restrictEnv,oneEach]) hm sep (by simp)
  obtain ⟨v,hv,he⟩ := hw C.output
  have eq : v.1 = Finset.univ.offDiag := by
    ext p
    have hp := Set.ext_iff.mp he p
    change (p ∈ v.1) ↔ C.eval (oneEach (e p.1) (e p.2)) = true at hp
    rw [rep (e p.1) (e p.2)] at hp
    simpa using hp
  simpa using marker_trace_crown tr hv eq

theorem crown_many_saturated (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) :
    4 ≤ (Finset.univ.filter (fun i : Fin 12 => 2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)).card := by
  classical
  let S := Finset.univ.filter (fun i : Fin 12 => (trueOrFlags C.gates (oneEach i i)).count true ≤ 1)
  let e : Fin S.card ↪ Fin 12 := (S.orderIsoOfFin rfl).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  have sub : ∀ i, (trueOrFlags C.gates (oneEach (e i) (e i))).count true ≤ 1 :=
    fun i => (Finset.mem_filter.mp ((S.orderIsoOfFin rfl i).property)).2
  have bd := subcrown_four_and e C hm rep sub
  have old := crown_size_forty_requires_twenty_three_ors C hm rep size
  have part := and_or_partition C.gates (fun g h => (hm g h).1)
  change C.gates.length ≤ 40 at size
  have hs : S.card ≤ 8 := by
    by_contra! h
    have prod := Nat.mul_le_mul (show 9 ≤ S.card by omega) (show 8 ≤ S.card-1 by omega)
    omega
  have comp := Finset.card_filter_add_card_filter_not (s := Finset.univ) (fun i : Fin 12 =>
    (trueOrFlags C.gates (oneEach i i)).count true ≤ 1)
  change S.card + _ = _ at comp
  have ge : 4 ≤ (Finset.univ.filter (fun i : Fin 12 =>
      ¬(trueOrFlags C.gates (oneEach i i)).count true ≤ 1)).card := by
    simp only [Finset.card_univ,Fintype.card_fin] at comp
    omega
  apply ge.trans
  apply Finset.card_le_card
  intro i hi
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_univ _,?_⟩
  have low := (Finset.mem_filter.mp hi).2
  omega

end CrownDiagonalCharge
