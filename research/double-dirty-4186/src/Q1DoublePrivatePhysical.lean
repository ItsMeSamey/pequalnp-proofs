import DDGuardClauses
import Q1DoublePhysicalPrice
import Q1DoublePrivateSignals

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle
open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover

abbrev Pin := ℕ × Fin 2

theorem two_boundary {n : ℕ} {C : Circuit} (A : Finset ℕ) (ne : A.Nonempty)
    (back : ∀ j ∈ A, ∀ b, opnd C j b < n+j) : 2 ≤ (occurrences n C A).card := by
  classical
  let j := A.min' ne
  have ja : j ∈ A := Finset.min'_mem _ _
  have hp (b : Fin 2) : (j,b) ∈ occurrences n C A := by
    apply Finset.mem_sdiff.mpr
    refine ⟨Finset.mem_product.mpr ⟨ja,Finset.mem_univ _⟩,?_⟩
    intro h
    obtain ⟨i,hi,eq⟩ := (Finset.mem_filter.mp h).2
    have h₁ := back j ja b
    have h₂ := Finset.min'_le A i hi
    change opnd C j b = n+i at eq
    change j ≤ i at h₂
    omega
  have sub : ({(j,0),(j,1)} : Finset Pin) ⊆ occurrences n C A := by
    intro p hin
    simp only [Finset.mem_insert,Finset.mem_singleton] at hin
    rcases hin with rfl | rfl <;> apply hp
  simpa using Finset.card_le_card sub

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Triangle

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

noncomputable def indexedLeaf (n : ℕ) (C : Circuit) (K : Finset (ℕ × Fin 2))
    (i : Fin K.card) : Private.Clause n := leafSupport n C (K.equivFin.symm i).val

private theorem indexedSem (K : Finset (ℕ × Fin 2)) (x : Fin n → Bool) :
    (∀ p ∈ K, ∃ z ∈ leafSupport n C p, x z=true) ↔
    ∀ i, ∃ z ∈ indexedLeaf n C K i, x z=true := by
  constructor
  · exact fun h i => h _ (K.equivFin.symm i).property
  · intro h p hp
    simpa [indexedLeaf] using h (K.equivFin ⟨p,hp⟩)

theorem physicalDesc {m : ℕ} (d : DoubleDirty G C m) (four : NoFourCycle G)
    (least : IsLeastAO G C) (A W : Finset (ℕ × Fin 2)) (term : (Fin n → Bool) → Bool)
    (plain : ∀ p ∈ A∪W, PlainWire n C m (opnd C p.1 p.2))
    (sem : ∀ x, term x=true ↔
      (∀ p ∈ A, ∃ z ∈ leafSupport n C p, x z=true) ∧
      (∀ p ∈ W, ∃ z ∈ leafSupport n C p, x z=true)) :
    ClauseSignal G C term (indexedLeaf n C A) (indexedLeaf n C W) := by
  constructor
  · intro x
    rw [sem,indexedSem,indexedSem]
    exact ⟨fun h c => Sum.rec h.1 h.2 c, fun h => ⟨fun i => h (.inl i),fun i => h (.inr i)⟩⟩
  · have stars := region_clause_stars d four least (A∪W) plain
    intro c
    cases c with
    | inl i => exact stars _ (Finset.mem_image.mpr ⟨_,Finset.mem_union_left _ (A.equivFin.symm i).property,rfl⟩)
    | inr i => exact stars _ (Finset.mem_image.mpr ⟨_,Finset.mem_union_right _ (W.equivFin.symm i).property,rfl⟩)

theorem finishPhysicalPrivate {m a b H : ℕ} (D : Allocation G C) (d : DoubleDirty G C m)
    (four : NoFourCycle G) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (pinsM : (gateAt C m).inputs = [n+a,n+b]) (ja : a∈junk G C) (jb : b∈junk G C)
    (ht : H∈tops G C) (aff : Influence n C m (n+H))
    (present : D.pivot∈D.components) (paid : ∀ i∈D.components.erase D.pivot, D.Local i)
    (res : D.edges D.pivot ⊆ Ustar G C) (accepted : D.edges D.pivot ⊆ gammaE G C H)
    (apart : Disjoint (andRegion n C a) (andRegion n C b))
    (guardApart : Disjoint (andRegion n C a ∪ andRegion n C b) ((andRegion n C H).erase H))
    (pool : andRegion n C a ∪ andRegion n C b ∪ (andRegion n C H).erase H ⊆ D.dirty D.pivot)
    (central : H∈D.roots D.pivot) : Positive G C := by
  classical
  obtain ⟨p,hp,_,nonempty,_,plainW,guard⟩ := guard_clause_decomposition d edge least form ht aff
  let W := (leaves n C H).erase p
  obtain ⟨ha,opa,_⟩ := (S4183.junk_iff G C a).mp ja
  obtain ⟨hb,opb,_⟩ := (S4183.junk_iff G C b).mp jb
  obtain ⟨hr,oph,below⟩ := Finset.mem_filter.mp ht
  have memA : n+a∈(gateAt C m).inputs := by simp [pinsM]
  have memB : n+b∈(gateAt C m).inputs := by simp [pinsM]
  have leftPlain := arm_boundary_plain d least.1 memA
  have rightPlain := arm_boundary_plain d least.1 memB
  have armDesc (r : ℕ) (bound : r<C.gates.length) (andR : (gateAt C r).op=.and)
      (plain : ∀ q∈leaves n C r, PlainWire n C m (opnd C q.1 q.2)) :
      ClauseSignal G C (fun x => gateVal n C r x && clauseConjunction n C W x)
        (indexedLeaf n C (leaves n C r)) (indexedLeaf n C W) := by
    apply physicalDesc d four least
    · intro q hq
      exact (Finset.mem_union.mp hq).elim (plain q) (plainW q)
    · intro x
      rw [Bool.and_eq_true,region_clause_semantics d least.1 form bound andR plain x]
      simp [clauseConjunction]
  have two (r : ℕ) (bound : r<C.gates.length) (andR : (gateAt C r).op=.and) : 2≤(leaves n C r).card := by
    apply Triangle.two_boundary _ ⟨r,root_mem_region bound andR⟩
    intro j hj k
    obtain ⟨_,u,v,ps,hu,hv⟩ := AO_of_IsAO2 n C least.1 j (in_region.mp hj).1
    fin_cases k <;> simp_all [opnd]
  have price := physical_mixer_price n C ∅ (andRegion n C a) (andRegion n C b) (andRegion n C H)
    (D.dirty D.pivot) (D.roots D.pivot) (fun _ => ∅) a b H id p (fun _ => ∅)
    (root_mem_region ha opa) (root_mem_region hb opb) (root_mem_region (Finset.mem_range.mp hr) oph)
    (by simp) (region_used least.1 a) (region_used least.1 b) (region_used least.1 H) (by simp)
    hp (by simp) (by simp) apart guardApart (by simp) (by simpa using pool) central
    (by simp) (by simp) (by simp)
  refine D.finishPrivateSignals four edge least form (by simp [d.exception]) present paid res accepted below
    (two a ha opa) (two b hb opb) (Finset.card_pos.mpr nonempty)
    _ _ _ _ _ ?_ (armDesc a ha opa leftPlain) (armDesc b hb opb rightPlain) ?_
  · intro x
    obtain ⟨hm,orm,_⟩ := mixer_info d
    have mix := W_or n C x m hm orm (n+a) (n+b) pinsM
      (least.1.2.1 m hm _ memA) (least.1.2.1 m hm _ memB)
    change gateVal n C m x = (gateVal n C a x || gateVal n C b x) at mix
    rw [guard x,mix]
    change ((_ || _) && clauseConjunction n C W x) = _
    cases clauseConjunction n C W x <;> simp
  · simpa [W,allowance,leaves] using price

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Allocation
