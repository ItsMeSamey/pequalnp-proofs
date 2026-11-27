import DDGuardRegion
import DDMixerGuard

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable def clauseConjunction (n : ℕ) (C : Circuit) (K : Finset (ℕ × Fin 2)) (x : Fin n → Bool) : Bool := by
  classical
  exact decide (∀ p ∈ K, ∃ z ∈ leafSupport n C p, x z = true)

private theorem clauseConjunction_truth (K : Finset (ℕ × Fin 2)) (x : Fin n → Bool) :
    clauseConjunction n C K x = true ↔ ∀ p ∈ K, ∃ z ∈ leafSupport n C p, x z = true := by
  simp [clauseConjunction]

theorem guard_clause_decomposition {m H : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (ht : H ∈ tops G C)
    (affected : Influence n C m (n+H)) :
    ∃ p ∈ leaves n C H, opnd C p.1 p.2 = n+m ∧
      let K := (leaves n C H).erase p
      K.Nonempty ∧ K.card ≤ ((andRegion n C H).erase H).card + 1 ∧
      (∀ q ∈ K, PlainWire n C m (opnd C q.1 q.2)) ∧
      (∀ x, gateVal n C H x = (gateVal n C m x && clauseConjunction n C K x)) := by
  classical
  obtain ⟨p,⟨pm,peq⟩,unique⟩ := unique_mixer_pin D edge least form ht affected
  let K := (leaves n C H).erase p
  have raw (q) (hq : q∈K) : PlainWire n C m (opnd C q.1 q.2) := by
    obtain ⟨ne,mem⟩ := Finset.mem_erase.mp hq
    rcases region_boundary_kind (m := m) least.1 mem with eq | yes
    · exact (ne (unique q ⟨mem,eq⟩)).elim
    · exact yes
  obtain ⟨hb,hand,below⟩ := Finset.mem_filter.mp ht
  have hr := Finset.mem_range.mp hb
  have sem (x : Fin n → Bool) :
      gateVal n C H x = (gateVal n C m x && clauseConjunction n C K x) := by
    rw [Bool.eq_iff_iff,region_eval least.1 hr hand x,Bool.and_eq_true,clauseConjunction_truth]
    constructor
    · intro yes
      refine ⟨?_,fun q hq => ?_⟩
      · have := yes p pm
        simpa only [peq,W,gateVal] using this
      · exact (leaf_semantics D least.1 form (Finset.mem_of_mem_erase hq) (raw q hq) x).mp
          (yes q (Finset.mem_of_mem_erase hq))
    · rintro ⟨hm,h⟩ q hq
      by_cases eq : q=p
      · subst q
        simpa only [peq,W,gateVal] using hm
      · have mem : q ∈ K := Finset.mem_erase.mpr ⟨eq,hq⟩
        exact (leaf_semantics D least.1 form hq (raw q mem) x).mpr (h q mem)
  have someLeaf : K.Nonempty := by
    by_contra h
    have empty := Finset.not_nonempty_iff_eq_empty.mp h
    apply (mixer_info D).2.2
    intro x hx
    apply below x
    simpa [hx,empty,clauseConjunction] using sem x
  have cap := guard_occurrences n C _ H (root_mem_region hr hand) (region_used least.1 H) p pm
  exact ⟨p,pm,peq,someLeaf,cap,raw,sem⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
