import Graph18272Bridge
import Q0Matching

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

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

theorem frontierClauseStars (h4 : NoFourCycle G) (hL : IsLeastAO G C)
    (hq : (orN G C \ lam G C).card = 0) (frontier : Finset ℕ)
    (raw : ∀ w ∈ frontier, w < n ∨ ∃ k < C.gates.length,
      w = n+k ∧ (gateAt C k).op = GateOp.or) :
    clauseStars G C (frontier.image (orIn n C)) := by
  intro K hK p hp q hq' hpq
  obtain ⟨w, hw, rfl⟩ := Finset.mem_image.mp hK
  rcases raw w hw with hi | ⟨k,hk,rfl,hor⟩
  · exact (hpq (Finset.card_le_one.mp (orIn_input C w hi) p hp q hq')).elim
  have hn : ¬ BelowF G C k := by
    intro hb
    have hv := S90.reach_var_val (pairInput p p) (n+k) p
      (S90.mem_orIn_reach p hp) (S90.pairInput_left p p)
    exact G.loopless.irrefl p ((S90.graphFun_pair G p p).mp (hb _ hv))
  have hN : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk, hor, hn⟩
  have hLam : k ∈ lam G C := by
    by_contra hh
    have hm := Finset.mem_sdiff.mpr ⟨hN,hh⟩
    rw [Finset.card_eq_zero.mp hq] at hm
    simpa using hm
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

end PEqualNP.Outside.L_meta_4186_aux.Q0
