import Graph18272Bridge
import Q0Matching
import Q1PureBase

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.S4183

attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

private theorem starredCross {a : ℕ} (ha : a ∈ tops G C) {x y : Fin n}
    (hx : x ∈ side (n := n) C a 0) (hy : y ∈ side (n := n) C a 1) :
    s(x,y) ∈ starEdges G C := by
  simp only [starEdges, Finset.mem_biUnion, Finset.mem_image, Finset.mem_product]
  exact ⟨a, ha, (x,y), ⟨hx,hy⟩, rfl⟩


structure PureException (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (e : ℕ) : Prop where
  exception : orN G C \ lam G C = {e}
  pure : ∀ j, InCone n C j e → (gateAt C j).op = GateOp.or

def Anchored (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (K : Finset (Fin n)) : Prop :=
  ∃ v, ∀ z ∈ K, G.Adj v z ∧ s(v,z) ∈ starEdges G C

theorem pureException_of_card {e : ℕ} (hq : (orN G C \ lam G C).card = 1)
    (he : e ∈ orN G C \ lam G C) (pure : ∀ j, InCone n C j e → (gateAt C j).op = GateOp.or) :
    PureException G C e := by
  obtain ⟨k,hk⟩ := Finset.card_eq_one.mp hq
  rw [hk, Finset.mem_singleton] at he
  subst k
  exact ⟨hk,pure⟩

theorem exceptional_or {e : ℕ} (pe : PureException G C e) :
    e < C.gates.length ∧ (gateAt C e).op = GateOp.or ∧ ¬ BelowF G C e := by
  have he : e ∈ orN G C \ lam G C := by simp [pe.exception]
  obtain ⟨h,hop,hb⟩ := Finset.mem_filter.mp (Finset.mem_sdiff.mp he).1
  exact ⟨Finset.mem_range.mp h,hop,hb⟩

theorem lambda_anchor (h4 : NoFourCycle G) (hL : IsLeastAO G C) {k : ℕ}
    (hLam : k ∈ lam G C) : Anchored G C (orIn n C (n+k)) := by
  obtain ⟨_, _, _, a, hat, b, hcard, hr⟩ := Finset.mem_filter.mp hLam
  obtain ⟨v,hv⟩ := Finset.card_eq_one.mp hcard
  have hcenter : v ∈ side (n := n) C a (1-b) := by simp [hv]
  have hsub : ∀ z ∈ orIn n C (n+k), z ∈ side (n := n) C a b := by
    intro z hz
    exact S90.reach_mem_orIn z (((S90.orReaches_reach k _ hr).1).trans
      (S90.mem_orIn_reach z hz))
  have adj := (S90.top_facts G C h4 hL a hat).2.1
  refine ⟨v, ?_⟩
  intro z hz
  have hleaf := hsub z hz
  fin_cases b
  · change v ∈ side (n := n) C a 1 at hcenter
    exact ⟨(adj z hleaf v hcenter).symm,
      Sym2.eq_swap ▸ starredCross hat hleaf hcenter⟩
  · change v ∈ side (n := n) C a 0 at hcenter
    exact ⟨adj v hcenter z hleaf, starredCross hat hcenter hleaf⟩

theorem raw_alternative {e w : ℕ} (pe : PureException G C e)
    (four : NoFourCycle G) (least : IsLeastAO G C) (ne : w ≠ n+e)
    (kind : w < n ∨ ∃ k < C.gates.length, w = n+k ∧ (gateAt C k).op = GateOp.or) :
    (orIn n C w).card ≤ 1 ∨ Anchored G C (orIn n C w) := by
  rcases kind with h | ⟨k,hk,rfl,hor⟩
  · exact Or.inl (orIn_input C w h)
  by_cases hs : (orIn n C (n+k)).card ≤ 1
  · exact Or.inl hs
  obtain ⟨p,hp⟩ := Finset.card_pos.mp (show 0 < (orIn n C (n+k)).card by omega)
  have hn : ¬ BelowF G C k := by
    intro hb
    have hv := S90.reach_var_val (pairInput p p) (n+k) p
      (S90.mem_orIn_reach p hp) (S90.pairInput_left p p)
    exact G.loopless.irrefl p ((S90.graphFun_pair G p p).mp (hb _ hv))
  have hN : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hor,hn⟩
  apply Or.inr
  apply lambda_anchor four least
  by_contra hl
  have he := Finset.mem_sdiff.mpr ⟨hN,hl⟩
  rw [pe.exception, Finset.mem_singleton] at he
  exact ne (by omega)

theorem child_alternative {e : ℕ} (pe : PureException G C e)
    (four : NoFourCycle G) (least : IsLeastAO G C) (w : ℕ) (hw : w ∈ (gateAt C e).inputs) :
    (orIn n C w).card ≤ 1 ∨ Anchored G C (orIn n C w) := by
  have he := (exceptional_or pe).1
  have lt := least.1.2.1 e he w hw
  apply raw_alternative pe four least (by omega)
  by_cases hi : w < n
  · exact Or.inl hi
  let k := w-n
  have eq : w = n+k := by dsimp [k]; omega
  have ke : k < e := by omega
  have inh : InCone n C k e := (S90.inCone_iff n C k e).mpr
    ⟨he,k,ke,eq ▸ hw,Or.inl rfl⟩
  exact Or.inr ⟨k,by omega,eq,pe.pure k inh⟩

theorem exceptional_union {e : ℕ} (pe : PureException G C e) (ao : IsAO2 n C) :
    orIn n C (n+e) = orIn n C (opnd C e 0) ∪ orIn n C (opnd C e 1) := by
  obtain ⟨he,hor,_⟩ := exceptional_or pe
  obtain ⟨p,q,hin⟩ := List.length_eq_two.mp (ao.2.2 _ (S90.gateAt_mem he))
  have hp : p ∈ (gateAt C e).inputs := by simp [hin]
  have hq : q ∈ (gateAt C e).inputs := by simp [hin]
  ext z
  rw [orIn_gate, Finset.mem_union]
  constructor
  · rintro ⟨_,_,w,hw,_,hz⟩
    simp only [hin, List.mem_cons, List.not_mem_nil, or_false] at hw
    rcases hw with rfl | rfl
    · exact Or.inl (by simpa [opnd,hin] using hz)
    · exact Or.inr (by simpa [opnd,hin] using hz)
  · rintro (h | h)
    · exact ⟨he,hor,p,hp,ao.2.1 e he _ hp,by simpa [opnd,hin] using h⟩
    · exact ⟨he,hor,q,hq,ao.2.1 e he _ hq,by simpa [opnd,hin] using h⟩

theorem PureException.noDirtyOr {e : ℕ} (pe : PureException G C e) (hAO : IsAO2 n C) :
    NoDirtyOr G C := by
  intro j r hj hr hin hor
  obtain ⟨_, hand, _, x, hx, hbad⟩ := Finset.mem_filter.mp hj
  have ht : ¬ BelowF G C r := by
    intro hb
    have hstep : S90.OrStep n C (n+r) (n+j) :=
      ⟨r, hr, rfl, hor, hin, hAO.2.1 r hr _ hin⟩
    have hv : gateVal n C r x = true :=
      S90.orStep_up (x := List.ofFn x) (by simp) (.single hstep) hx
    have contra := hb x hv
    rw [hbad] at contra
    contradiction
  have hrN : r ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hor, ht⟩
  have hrLam : r ∈ lam G C := by
    by_contra hh
    have hm := Finset.mem_sdiff.mpr ⟨hrN, hh⟩
    rw [pe.exception, Finset.mem_singleton] at hm
    subst r
    have lt := hAO.2.1 e hr _ hin
    have hcone : InCone n C j e := (S90.inCone_iff n C j e).mpr
      ⟨hr,j,by omega,hin,Or.inl rfl⟩
    have hfalse := pe.pure j hcone
    rw [hand] at hfalse
    contradiction
  obtain ⟨_, h0, h1, _⟩ := Finset.mem_filter.mp hrLam
  have empty := Q0.and_empty_support (n := n) hand
  rcases Q0.reader_pin hAO hr hin with e | e
  · rw [e, empty] at h0
    simpa using h0
  · rw [e, empty] at h1
    simpa using h1

theorem child_pin_alternative {e : ℕ} (pe : PureException G C e)
    (four : NoFourCycle G) (least : IsLeastAO G C) (b : Fin 2) :
    (orIn n C (opnd C e b)).card ≤ 1 ∨ Anchored G C (orIn n C (opnd C e b)) := by
  apply child_alternative pe four least
  obtain ⟨p,q,hin⟩ := List.length_eq_two.mp (least.1.2.2 _ (S90.gateAt_mem (exceptional_or pe).1))
  fin_cases b <;> simp [opnd,hin]

theorem frontier_clauseStars_erase {e : ℕ} (pe : PureException G C e)
    (four : NoFourCycle G) (least : IsLeastAO G C) (F : Finset ℕ)
    (raw : ∀ w ∈ F, w < n ∨ ∃ k < C.gates.length, w = n+k ∧ (gateAt C k).op = GateOp.or) :
    Q0.clauseStars G C ((F.image (orIn n C)).erase (orIn n C (n+e))) := by
  intro K hK p hp q hq hpq
  obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hK
  obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp mem
  have wn : w ≠ n+e := fun h => ne (congrArg (orIn n C) h)
  rcases raw_alternative pe four least wn (raw w hw) with h | h
  · exact (hpq (Finset.card_le_one.mp h p hp q hq)).elim
  · exact h

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
