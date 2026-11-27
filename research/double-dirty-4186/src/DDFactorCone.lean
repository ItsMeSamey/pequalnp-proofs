import DDFactorAgreement
import Q1DoubleSplitCost
import Q0FactorPinRules

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

/-- These paths follow actual pins, regardless of which operation reads them. -/
inductive Influence (n : ℕ) (C : Circuit) (g : ℕ) : ℕ → Prop
  | source : Influence n C g (n+g)
  | step {j w : ℕ} (prev : Influence n C g w) (bound : j < C.gates.length)
      (pin : w ∈ (gateAt C j).inputs) : Influence n C g (n+j)

abbrev factorCuts (n : ℕ) (C : Circuit) (T : Finset ℕ) (g : ℕ) : Cuts :=
  ⟨fun j => decide (j ∈ T), fun j b => decide (opnd C j b = n+g)⟩

theorem opnd_mem {n : ℕ} {C : Circuit} (ao : IsAO2 n C) {j : ℕ}
    (hj : j < C.gates.length) (b : Fin 2) : opnd C j b ∈ (gateAt C j).inputs := by
  obtain ⟨_,a,b',pins,_,_⟩ := AO_of_IsAO2 n C ao j hj
  fin_cases b <;> simp [opnd,pins]

theorem kept_nonclean {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) {j : ℕ} (hj : j < C.gates.length) (w : ℕ)
    (keep : Kept G C (n+j)) (pin : w ∈ (gateAt C j).inputs) : Kept G C w := by
  obtain ⟨read,out,_⟩ := main_real n G C edge least form
  intro i hi he
  obtain ⟨ir,_,hb⟩ := Finset.mem_filter.mp hi
  have reader : j ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, he ▸ pin⟩
  have neq : n+i ≠ C.output := by
    intro eq
    have ix : C.output-n = i := by omega
    rw [ix] at out
    simpa [out] using reader
  obtain ⟨r,single,orr,below⟩ := read i (Finset.mem_range.mp ir) hb neq
  rw [single,Finset.mem_singleton] at reader
  subst r
  exact keep j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,orr,below⟩) rfl

/-- For ordinary extraction use omitSource=false. For physical splitting, the mixer
itself is also omitted. The root-specific hypothesis is vacuous for unaffected roots. -/
theorem safe_factor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (omitSource : Bool) (x : Fin n → Bool) :
    Safe C (if omitSource then splitCuts n C (orT G C) g else factorCuts n C (orT G C) g) x
      (fun w => Kept G C w ∧ (Influence n C g w → W n C x (n+g) = true)) := by
  cases omitSource <;> constructor
  all_goals try
    (intro j hj h om
     have notClean : j ∉ orT G C := fun hm => h.1 j hm rfl
     simp [splitCuts,factorCuts,notClean] at om
     subst j
     exact h.2 .source)
  all_goals try
    (intro j hj h om
     have notClean : j ∉ orT G C := fun hm => h.1 j hm rfl
     simp [splitCuts,factorCuts,notClean] at om
     done)
  all_goals
    intro j hj h _ b
    have mem := opnd_mem least.1 hj b
    have prior := kept_nonclean edge least form hj _ h.1 mem
    by_cases he : opnd C j b = n+g
    · rw [he] at mem
      have source := h.2 (.step .source hj mem)
      simpa [splitCuts,factorCuts,he] using source
    · have invariant : Kept G C (opnd C j b) ∧
          (Influence n C g (opnd C j b) → W n C x (n+g) = true) :=
        ⟨prior, fun path => h.2 (.step path hj mem)⟩
      simpa [splitCuts,factorCuts,he] using invariant

theorem root_cofactor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (omitSource : Bool) {w : ℕ} (hw : w < n+C.size)
    (keep : Kept G C w) (x : Fin n → Bool)
    (enabled : Influence n C g w → W n C x (n+g) = true) :
    W n C x w = denotation (physicalSlot n C
      (if omitSource then splitCuts n C (orT G C) g else factorCuts n C (orT G C) g) C.size w) x :=
  agree C least.1 _ x _ (safe_factor G C g edge least form omitSource x) C.size le_rfl w hw ⟨keep,enabled⟩

theorem source_slot_original {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hg : g < C.size) (keep : Kept G C (n+g))
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (x : Fin n → Bool) : W n C x (n+g) =
      denotation (physicalSlot n C (factorCuts n C (orT G C) g) C.size (n+g)) x := by
  let need := fun w => Kept G C w ∧ w ≤ n+g
  have sf : Safe C (factorCuts n C (orT G C) g) x need := by
    constructor
    · intro j _ want omittedRow
      have contra : j ∉ orT G C := fun h => want.1 j h rfl
      simp [factorCuts,contra] at omittedRow
    · intro j hj want _ d
      have hm := opnd_mem least.1 hj d
      have lt := least.1.2.1 j hj _ hm
      have le : n+j ≤ n+g := want.2
      have neq : opnd C j d ≠ n+g := by omega
      simp only [factorCuts, decide_eq_true_eq, neq, and_false, if_false]
      exact ⟨kept_nonclean edge least form hj _ want.1 hm, by omega⟩
  exact agree C least.1 _ x need sf C.size le_rfl _ (by omega) ⟨keep,le_rfl⟩

theorem zero_wire {n : ℕ} (C : Circuit) (ao : IsAO2 n C) (w : ℕ) (hw : w < n+C.size) :
    W n C (fun _ => false) w = false := by
  induction w using Nat.strong_induction_on with
  | _ w ih =>
    by_cases raw : w < n
    · exact W_input n C (fun _ => false) w raw
    obtain ⟨i,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt raw)
    have hi : i < C.gates.length := by change n+i < n+C.gates.length at hw; omega
    obtain ⟨ops,a,b,inputs,ha,hb⟩ := AO_of_IsAO2 n C ao i hi
    have av := ih a ha (ha.trans hw)
    have bv := ih b hb (hb.trans hw)
    rcases ops with op|op
    · simp [W_and n C (fun _ => false) i hi op a b inputs ha hb,av,bv]
    · simp [W_or n C (fun _ => false) i hi op a b inputs ha hb,av,bv]

theorem source_in_bank {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (hg : g < C.size) (keep : Kept G C (n+g))
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    {B : Bank n} (slots : ∀ w, physically B (physicalSlot n C (factorCuts n C (orT G C) g) C.size w)) :
    B (gateVal n C g) := by
  have fact := source_slot_original G C g hg keep edge least form
  have ready := slots (n+g)
  cases he : physicalSlot n C (factorCuts n C (orT G C) g) C.size (n+g) with
  | none =>
    have bad := fact (fun _ => false)
    rw [he,zero_wire C least.1 _ (by omega)] at bad
    simp [denotation] at bad
  | some f =>
    have ids : gateVal n C g = f := funext fun x => by
      change W n C x (n+g) = f x
      simpa [he,denotation] using fact x
    rw [ids]
    simpa [he,physically] using ready

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
