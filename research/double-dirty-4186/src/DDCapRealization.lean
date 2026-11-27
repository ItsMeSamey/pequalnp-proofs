import DDVirtualEvidence
import DDGraphIndexedSplit
import DDIndexedRootCover
import DDIndexedRootMap
import DDIndexedDominance
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double Indexed Virtual
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
theorem cap_of_isolation (s : OriginalCut G C)
    (apart : ∀ (z : SplitData G C s.mixer) (A B W : Origin × ℕ),
      let p := splitCuts n C (orT G C) s.mixer
      ref (build n C p C.size) (n+z.a) = some A →
      ref (build n C p C.size) (n+z.b) = some B →
      ref (build n C p C.size) (n+z.t) = some W →
      ∀ r∈rootIndices n C p ((tops G C).erase s.top),
      ∀ t∈rootIndices n C p ((tops G C).erase s.top),
      ¬strictInfluence n (capPrefix n C p C.size A.2 B.2 W.2) r (n+t)) :
    Nonempty (CapRealization s) := by
  classical
  obtain ⟨z,_,A,B,W,_,ra,rb,rw',_⟩ := graph_indexed_split G C s.mixer s.double s.edge s.least s.form
  let p := splitCuts n C (orT G C) s.mixer
  let E := (tops G C).erase s.top
  have zt : s.top=z.t := z.onlyAffected _ (Finset.mem_filter.mp s.centrelessTop).1 s.influence
  let a : Fin (n+rank n C p C.size) := ⟨A.2,ref_bound ra⟩
  let b : Fin (n+rank n C p C.size) := ⟨B.2,ref_bound rb⟩
  let w : Fin (n+rank n C p C.size) := ⟨W.2,ref_bound rw'⟩
  let D := capPrefix n C p C.size a b w
  have Esub : E ⊆ Finset.range C.size := fun i hi => (Finset.mem_filter.mp (Finset.mem_erase.mp hi).2).1
  have EB : E.card ≤ (orT G C).card := by
    have q := Q0.clean_or_count G C s.edge s.least s.form
    have mem := (Finset.mem_filter.mp s.centrelessTop).1
    change ((tops G C).erase s.top).card ≤ _
    rw [Finset.card_erase_of_mem mem];omega
  let F : RootForest G C :=
    { net := D
      ao := (cap_prefix_spec C p s.least.1 le_rfl a b w).1
      roots := rootIndices n C p E
      valid := fun _ hr => root_valid Esub a b w hr
      near := root_budget s.double s.edge s.least E EB a b w
      cover := fun x => by
        have h := cap_cover s.double s.edge s.least s.form z a b w A.1 B.1 W.1 ra rb rw' x
        simpa only [E,zt] using h }
  let arms := opnd C s.mixer
  let AW (t : Fin 2) : Origin × ℕ := if t=0 then A else B
  have armRefs (t : Fin 2) : ref (build n C p C.size) (arms t) = some (AW t) := by
    fin_cases t
    · change ref (build n C p C.size) (opnd C s.mixer 0) = some A
      rw [z.left]
      exact ra
    · simpa [arms,z.right,AW] using rb
  have guardRef : ref (build n C p C.size) (n+s.top) = some W := zt.symm ▸ rw'
  have pre : D.gates = (build n C p C.size).gates ++
      (⟨.and,[(AW 0).2,W.2]⟩ :: ⟨.and,[(AW 1).2,W.2]⟩ :: []) := rfl
  have extPaid (i : ℕ) (hi : i ∈ E) : i<C.size ∧ ∃ g, ins n C p i = some g := by
    obtain ⟨ne,top⟩ := Finset.mem_erase.mp hi
    have off : ¬ Influence n C s.mixer (n+i) := fun h => ne ((z.onlyAffected i top h).trans zt.symm)
    exact ⟨Finset.mem_range.mp (Esub hi),external_paid s.edge s.least s.form top off⟩
  refine ⟨⟨F,nodeIndex n C p,?_,?_,?_,?_,?_,?_⟩⟩
  · intro i v hv
    cases v with
    | row j => exact row_reader C p E arms _ _ pre hv
    | arm t => exact arm_reader C p E arms _ AW W armRefs guardRef [] pre t hv
  · intro i hi
    obtain ⟨valid,paid,hand⟩ := Finset.mem_filter.mp hi
    have ilt := Finset.mem_range.mp valid
    change i < C.size at ilt
    change (ins n C p i).isSome = true at paid
    cases e : ins n C p i with
    | none => simp [e] at paid
    | some g =>
      have hphys : gateAt D (rank n C p i) = g := prefix_gate e ilt
      have hlt := paid_strict C p e ilt
      refine ⟨?_,?_⟩
      · change rank n C p i < D.size
        have hs := (cap_prefix_spec C p s.least.1 le_rfl a b w).2.1
        change D.size=rank n C p C.size+2 at hs
        omega
      · change (gateAt D (rank n C p i)).op=_
        rw [hphys,op_preserved e];exact hand
  · intro r hr; exact roots_mapped C p E arms _ hr
  · exact root_inj C p E arms _ extPaid
  · intro i j hop hj hpin
    exact cap_reader_and s.double s.least.1 le_rfl a b w hop hj hpin
  · exact apart z A B W ra rb rw'
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OriginalCut
