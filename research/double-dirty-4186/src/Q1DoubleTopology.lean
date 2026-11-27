import Graph18272Bridge
import Q0Routes

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open S4183
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

structure DoubleDirty (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ) : Prop where
  exception : orN G C \ lam G C = {m}
  pins : ∀ b : Fin 2, ∃ j ∈ junk G C, opnd C m b = n+j

theorem doubleDirty_of_card {m : ℕ} (q : (orN G C \ lam G C).card = 1)
    (hm : m ∈ orN G C \ lam G C)
    (pins : ∀ b : Fin 2, ∃ j ∈ junk G C, opnd C m b = n+j) : DoubleDirty G C m := by
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp q
  rw [hk, Finset.mem_singleton] at hm
  subst k
  exact ⟨hk,pins⟩

theorem mixer_info {m : ℕ} (D : DoubleDirty G C m) :
    m < C.gates.length ∧ (gateAt C m).op = GateOp.or ∧ ¬ BelowF G C m := by
  have h : m ∈ orN G C \ lam G C := by simp [D.exception]
  obtain ⟨hr,hor,hb⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1
  exact ⟨Finset.mem_range.mp hr,hor,hb⟩

theorem mixer_empty {m : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C) :
    orIn n C (n+m) = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro u hu
  obtain ⟨hr,_,w,hw,_,hs⟩ := (orIn_gate C m u).mp hu
  have pinEmpty (b : Fin 2) : orIn n C (opnd C m b) = ∅ := by
    obtain ⟨j,hj,eq⟩ := D.pins b
    rw [eq]
    exact Q0.and_empty_support ((junk_iff G C j).mp hj).2.1
  rcases Q0.reader_pin ao hr hw with e | e
  · rw [← e, pinEmpty] at hs
    simpa using hs
  · rw [← e, pinEmpty] at hs
    simpa using hs

private theorem empty_bad_or_eq {m j r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (bad : ¬ BelowF G C j) (empty : orIn n C (n+j) = ∅) (hr : r < C.gates.length)
    (pin : n+j ∈ (gateAt C r).inputs) (hor : (gateAt C r).op = GateOp.or) : r = m := by
  have hbad : ¬ BelowF G C r := by
    intro h
    apply bad
    intro x hx
    exact h x (S90.orStep_up (x := List.ofFn x) (by simp)
      (.single ⟨r,hr,rfl,hor,pin,ao.2.1 r hr _ pin⟩) hx)
  have hN : r ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hor,hbad⟩
  have hL : r ∉ lam G C := by
    intro hl
    obtain ⟨_,h0,h1,_⟩ := Finset.mem_filter.mp hl
    rcases Q0.reader_pin ao hr pin with e | e
    · rw [e,empty] at h0
      simpa using h0
    · rw [e,empty] at h1
      simpa using h1
  have he := Finset.mem_sdiff.mpr ⟨hN,hL⟩
  simpa only [D.exception, Finset.mem_singleton] using he

theorem dirty_or_eq {m j r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (hj : j ∈ junk G C) (hr : r < C.gates.length) (pin : n+j ∈ (gateAt C r).inputs)
    (hor : (gateAt C r).op = GateOp.or) : r = m := by
  obtain ⟨_,hand,bad⟩ := (junk_iff G C j).mp hj
  exact empty_bad_or_eq D ao bad (Q0.and_empty_support hand) hr pin hor

theorem no_mixer_or {m r : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (hr : r < C.gates.length) (pin : n+m ∈ (gateAt C r).inputs) :
    (gateAt C r).op ≠ GateOp.or := by
  intro hor
  have eq := empty_bad_or_eq D ao (mixer_info D).2.2 (mixer_empty D ao) hr pin hor
  have lt := ao.2.1 r hr _ pin
  omega

theorem pure_side_no_and (hao : IsAO2 n C) (htf : PEqualNP.TopForm.TopForm G C)
    {m : ℕ} (D : DoubleDirty G C m) {a w j : ℕ} (ha : a ∈ tops G C)
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
  rcases Relation.ReflTransGen.cases_tail reach with he | ⟨v, hbefore, hstep⟩
  · rw [← he, PEqualNP.Outside.L_meta_4186_aux.Q0.and_empty_support (n := n) hand] at hne
    simpa using hne
  · obtain ⟨r, hr, hv, hro, hpin, _⟩ := hstep
    have er := dirty_or_eq D hao hjunk hr hpin hro
    subst r
    rw [hv] at hbefore
    rcases Relation.ReflTransGen.cases_tail hbefore with ew | ⟨_, _, hlast⟩
    · rw [← ew, mixer_empty D hao] at hne
      simpa using hne
    · obtain ⟨t,ht,_,hot,hmt,_⟩ := hlast
      exact no_mixer_or D hao ht hmt hot

theorem noncentreless_accepted_star (hao : IsAO2 n C) (htf : PEqualNP.TopForm.TopForm G C)
    {m : ℕ} (D : DoubleDirty G C m) {a : ℕ}
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
    · exact (pure_side_no_and hao htf D hat hw hne hj hnor reach).elim
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

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
