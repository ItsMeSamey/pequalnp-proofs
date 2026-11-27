import Q0Readers

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q0ReaderDeps

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

theorem pure_side_no_and (hao : IsAO2 n C) (htf : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0) {a w j : ℕ} (ha : a ∈ tops G C)
    (hw : w ∈ (gateAt C a).inputs) (hne : (orIn n C w).Nonempty)
    (hj : j < C.gates.length) (hor : (gateAt C j).op ≠ GateOp.or)
    (reach : Relation.ReflTransGen (S90.OrStep n C) w (n+j)) : False := by
  obtain ⟨ha', hop, _⟩ := Finset.mem_filter.mp ha
  have haLt : a < C.gates.length := Finset.mem_range.mp ha'
  have hand := (hao.1 _ (S90.gateAt_mem hj)).resolve_right hor
  have hn : ¬ BelowF G C j := fun h => htf j hj a haLt hand h hop
    (S90.operand_cone haLt hw (hao.2.1 a haLt w hw) reach)
  have hjunk : j ∈ junk G C := by
    unfold junk gatesWhere
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hj, hand, hj, ?_⟩
    unfold BelowF at hn
    push_neg at hn
    obtain ⟨x, hx, hf⟩ := hn
    exact ⟨x, hx, by simpa using hf⟩
  rcases Relation.ReflTransGen.cases_tail reach with he | ⟨_, _, hstep⟩
  · rw [← he, and_empty_support (n := n) hand] at hne
    simpa using hne
  · obtain ⟨r, hr, _, hro, hpin, _⟩ := hstep
    exact dirty_reader_not_or hao hq hjunk hr hpin hro

theorem noncentreless_accepted_star (hao : IsAO2 n C) (htf : PEqualNP.TopForm.TopForm G C)
    (hq : (orN G C \ lam G C).card = 0) {a : ℕ}
    (ha : a ∈ tops G C \ centreless G C) (u v : Fin n)
    (hv : gateVal n C a (pairInput u v) = true) : s(u,v) ∈ starEdges G C := by
  obtain ⟨hat, hnc⟩ := Finset.mem_sdiff.mp ha
  obtain ⟨ha', hop, hbel⟩ := Finset.mem_filter.mp hat
  have halt : a < C.gates.length := Finset.mem_range.mp ha'
  obtain ⟨p, q, hin⟩ := List.length_eq_two.mp (hao.2.2 _ (S90.gateAt_mem halt))
  have e0 : opnd C a 0 = p := by simp [opnd, hin]
  have e1 : opnd C a 1 = q := by simp [opnd, hin]
  have hn0 : (orIn n C p).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hnc (Finset.mem_filter.mpr ⟨hat, Or.inl (by simpa [side, e0] using h)⟩)
  have hn1 : (orIn n C q).Nonempty := by
    apply Finset.nonempty_iff_ne_empty.mpr
    intro h
    exact hnc (Finset.mem_filter.mpr ⟨hat, Or.inr (by simpa [side, e1] using h)⟩)
  have raw : ∀ w ∈ (gateAt C a).inputs, (orIn n C w).Nonempty →
      ∃ t : Fin n, (t = u ∨ t = v) ∧ Relation.ReflTransGen (S90.OrStep n C) w t.val := by
    intro w hw hne
    have hval := ((S90.val_and (n := n) (by simp) halt hop).mp hv w hw).2
    rcases S90.operand_trace u v w hval with h | ⟨j, hj, hnor, reach, _⟩
    · exact h
    · exact (pure_side_no_and hao htf hq hat hw hne hj hnor reach).elim
  have hp : p ∈ (gateAt C a).inputs := by simp [hin]
  have hq' : q ∈ (gateAt C a).inputs := by simp [hin]
  obtain ⟨s, hs, hrs⟩ := raw p hp hn0
  obtain ⟨t, ht, hrt⟩ := raw q hq' hn1
  have adj := S90.side_adj G (graphFun G ∅) (fun i j => (S90.graphFun_pair G i j).mp)
    a halt hop hbel p q hin (hao.2.1 a halt p hp) (hao.2.1 a halt q hq') s t hrs hrt
  have hne := G.ne_of_adj adj
  have he : s(u,v) = s(s,t) := by
    rcases hs with h1 | h1 <;> rcases ht with h2 | h2
    · exact (hne (h1.trans h2.symm)).elim
    · rw [h1,h2]
    · rw [h1,h2]; exact Sym2.eq_swap
    · exact (hne (h1.trans h2.symm)).elim
  rw [he]
  simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  refine ⟨a, hat, (s,t), ⟨?_, ?_⟩, rfl⟩
  · simpa only [side, e0] using S90.reach_mem_orIn s hrs
  · simpa only [side, e1] using S90.reach_mem_orIn t hrt

end PEqualNP.Outside.L_meta_4186_aux.Q0
