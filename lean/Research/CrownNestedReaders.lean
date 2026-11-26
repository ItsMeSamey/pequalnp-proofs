import Research.CrownFirstSingleton
import Research.CrownOrPrefixReads

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem nest_zero_flag (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23) (h : Nat) :
    (trueOrFlags C.gates (List.replicate 24 false)).getD h false = false := by
  have no := List.count_eq_zero.mp (crown_allzero_no_or C hm rep size ors)
  let fs := trueOrFlags C.gates (List.replicate 24 false)
  change fs.getD h false = false
  by_cases small : h < fs.length
  · simp only [List.getD_eq_getElem?_getD,List.getElem?_eq_getElem small,Option.getD_some]
    cases e : fs[h] with
    | false => rfl
    | true => exact False.elim (no (e ▸ List.getElem_mem small))
  · exact getD_missing (by omega)

theorem nest_first_read (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (x : List Bool) (len : x.length = 24) (a : Fin 24)
    (single : ∀ j, x.getD j false = true ↔ j = a.val) (g : Nat)
    (on : (trueOrFlags C.gates x).getD g false = true)
    (before : ∀ j < g, (trueOrFlags C.gates x).getD j false = false) :
    a.val ∈ readAt C.gates 24 g := by
  obtain ⟨i,hi,hot⟩ := (flag_iff_final_parent _ _ _).mp on
  rw [len] at hi
  exact (minimal_crown_first_singleton_raw C hm rep mini size ors x len a single g i on before hi hot) ▸ hi

/-- The second OR of a nested pair reads the later sibling and the first OR's output. -/
theorem nested_second_readers (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (a b : Fin 24) (x y : List Bool) (lx : x.length = 24) (ly : y.length = 24)
    (sx : ∀ j, x.getD j false = true ↔ j = a.val) (sy : ∀ j, y.getD j false = true ↔ j = b.val)
    (g h : Fin C.gates.length) (gh : g < h)
    (onX : ∀ j, (trueOrFlags C.gates x).getD j false = true ↔ j = g.val ∨ j = h.val)
    (onY : ∀ j, (trueOrFlags C.gates y).getD j false = true ↔ j = h.val)
    (indep : Disjoint (readAt C.gates 24 g.val) (readAt C.gates 24 h.val)) :
    readAt C.gates 24 h.val = {b.val,24+g.val} := by
  have beforeX (j : Nat) (hj : j < g.val) : (trueOrFlags C.gates x).getD j false = false := by
    cases e : (trueOrFlags C.gates x).getD j false with
    | false => rfl
    | true => have := (onX j).mp e; omega
  have beforeY (j : Nat) (hj : j < h.val) : (trueOrFlags C.gates y).getD j false = false := by
    cases e : (trueOrFlags C.gates y).getD j false with
    | false => rfl
    | true => have := (onY j).mp e; omega
  have onG := (onX g.val).mpr (Or.inl rfl)
  have ra := nest_first_read C hm rep mini size ors x lx a sx _ onG beforeX
  have rb := nest_first_read C hm rep mini size ors y ly b sy _ ((onY _).mpr rfl) beforeY
  have noA := Finset.disjoint_left.mp indep ra
  have onH := (onX h.val).mpr (Or.inr rfl)
  obtain ⟨i,ri,hot⟩ := (flag_iff_final_parent _ _ _).mp onH
  rw [lx] at ri
  have bound := nest_read_lt C.gates 24 h.val i ri
  have mono := fun (op : Gate) (hg : op ∈ C.gates) => (hm op hg).1
  let X := {w : List Bool // w.length = 24}
  let W (j : Nat) := {q : X | (C.wires q.val).getD j false = true}
  have lit (q : X) (v : q.val.getD a.val false = true) :
      ((Circuit.mk C.gates 0).wires q.val).getD (24+g.val) false = true := by
    have hit : ((Circuit.mk C.gates 0).wires q.val).getD a.val false = true :=
      (nest_input_preserved C.gates q.val a.val (by rw [q.property]; exact a.isLt)).trans v
    have fg := (flag_iff_final_parent C.gates q.val g.val).mpr ⟨a.val,by simpa only [q.property] using ra,hit⟩
    rw [nest_flag_as_wire C.gates x q.val g.val onG,q.property] at fg
    exact fg
  have chain := nest_predecessor_semantics C.gates 24 ⟨x,lx⟩ a.val g.val h.val i sx mono onG
    (fun j hj hp => ((onX j).mp hp).resolve_right (by omega)) lit bound hot
  change W i = {q : X | q.val.getD a.val false = true} ∨ W i = W (24+g.val) ∨ W i = Set.univ at chain
  have rawW : W a.val = {q : X | q.val.getD a.val false = true} := by
    ext q
    simp only [W,Set.mem_ofPred_eq]
    rw [show (C.wires q.val).getD a.val false = q.val.getD a.val false from
      nest_input_preserved _ _ _ (by rw [q.property]; exact a.isLt)]
  have nocopy (j k : Nat) (hk : k < j) (hj : 24 ≤ j) (valid : j < 24+C.gates.length)
      (eq : W j = W k) : False := by
    let r := j-24
    have ej : 24+r = j := by dsimp [r]; omega
    apply minimal_crown_no_earlier_copy C hm rep mini ors r k (by dsimp [r]; omega) (by omega)
    intro u v
    let q : X := ⟨oneEach u v,by simp [oneEach]⟩
    rw [ej]
    have equiv : (C.wires q.val).getD j false = true ↔ (C.wires q.val).getD k false = true :=
      Set.ext_iff.mp eq q
    exact Bool.eq_iff_iff.mpr equiv
  have isG : i = 24+g.val := by
    rcases chain with raw|first|full
    · by_cases hi : i < 24
      · have same := (sx i).mp ((nest_input_preserved C.gates x i (by omega)).symm.trans hot)
        exact (noA (same ▸ ri)).elim
      · exact (nocopy i a.val (by omega) (by omega) (by omega) (raw.trans rawW.symm)).elim
    · by_contra ne
      rcases Nat.lt_or_gt_of_ne ne with less|more
      · exact nocopy (24+g.val) i less (by omega) (by omega) first.symm
      · exact nocopy i (24+g.val) more (by omega) (by omega) first
    · let q : X := ⟨List.replicate 24 false,by simp⟩
      have live : q ∈ W i := full.symm ▸ Set.mem_univ q
      have fg := (flag_iff_final_parent C.gates q.val h.val).mpr ⟨i,by simpa only [q.property] using ri,live⟩
      exact Bool.noConfusion ((nest_zero_flag C hm rep size ors h.val).symm.trans fg)
  have both : ({b.val,24+g.val} : Finset Nat) ⊆ readAt C.gates 24 h.val := by
    intro j hj
    rcases Finset.mem_insert.mp hj with e|e
    · exact e ▸ rb
    · exact (Finset.mem_singleton.mp e) ▸ (isG ▸ ri)
  apply (Finset.eq_of_subset_of_card_le both _).symm
  simpa [show b.val ≠ 24+g.val by omega] using
    readAt_card_le_two C.gates 24 h.val (fun op hh => (hm op hh).2)

end PEqualNP.Research.MissingCell
