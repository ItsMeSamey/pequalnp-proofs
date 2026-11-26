import ThresholdFanoutBudget
import ThresholdDegreeBudget
import ThresholdEndpointComponents
import ThresholdPublicMinimum

namespace ThresholdGlobalGlue
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus
open ThresholdOrGroups ThresholdOrExtraction ThresholdSimpleIncidence ThresholdRegularSource
open T2SoleOrSplice T2CubeDeletion ThresholdFanoutBudget ThresholdGraphCounts

theorem count_partition (C : Circuit) : (andIds C).length + ors C.gates = C.gates.length := by
  have flag (i : T2OrPartition.Id C) :
      T2OrPartition.isOr C i = ThresholdOrGroups.isOr (C.gates.get i) := rfl
  have part (xs : List (T2OrPartition.Id C)) :
      (xs.filter (fun i => !T2OrPartition.isOr C i)).length +
      (xs.map C.gates.get).countP ThresholdOrGroups.isOr = xs.length := by
    induction xs with
    | nil => rfl
    | cons i xs ih =>
      cases h : T2OrPartition.isOr C i <;> have e := (flag i).symm.trans h <;>
        simp only [List.filter_cons,List.map_cons,List.countP_cons,h,e,Bool.not_true,
          Bool.not_false,Bool.false_eq_true,ite_true,ite_false,List.length_cons] <;> omega
  simpa [andIds,ors] using part (List.finRange C.gates.length)

attribute [local instance] Classical.propDecidable

theorem regular_ledger {n out : Nat} {gs : List Raw}
    (M : LexMinimum n (source gs out)) (reg : T2RegularOrDelete.Regular n gs)
    (two : ∀ w,(endpoints (layout n gs out M.eligible) w).card=2)
    (inj : Function.Injective (endpoints (layout n gs out M.eligible)))
    (D : Circuit) (dm : Monotone2 D)
    (rep : ∀ s : Finset (Fin n), D.eval (incidence (endpointLists (layout n gs out M.eligible))
      (vector s))=true ↔ 2≤s.card)
    (price : ors D.gates + 2*n ≤ ors (source gs out).gates + (vertices (layout n gs out M.eligible)).card) :
    Nonempty (ThresholdFourThirds.Regular (n:ℤ) (((source gs out).size:ℤ)-2*(n:ℤ))) := by
  classical
  let B := source gs out
  let L := layout n gs out M.eligible
  let c := Nat.card (graph L).ConnectedComponent
  let a := (andIds B).length
  let v := (vertices L).card
  let o := ors B.gates
  let d := o+4+c-2*n
  have full : Computes n B := M.eligible.1
  have mono : Monotone2 B := ThresholdPublicMinimum.eligible_mono M.eligible
  have floor : 2*n-4 ≤ o := original_or_floor B mono full
  have part : a+o = B.size := count_partition B
  have fan : v+2*n ≤ 2*a+B.size+2 := by
    change (vertices L).card+2*n ≤ _
    rw [vertices_card]
    exact regular_vertex_budget M reg
  have degree (u : Vtx L) : (rawAt L u).card ≤ d := by
    rw [←degree_eq_raw L u two inj]
    have h : (graph L).degree u+2*n≤o+4+c := physical_degree_budget L u mono full two inj D dm rep price
    dsimp only [d]
    omega
  have comp : 2*c ≤ v := ThresholdEndpointBound.endpoint_components L two inj
  have edges : 2*n ≤ 2*c+(v-2*c)*(d+2) := ThresholdEndpointBound.endpoint_edges L two inj degree
  have castEdges : 2*(n:ℤ) ≤ 2*(c:ℤ)+((v:ℤ)-2*(c:ℤ))*((d:ℤ)+2) := by
    have h : ((2*n : Nat):ℤ) ≤ ((2*c+(v-2*c)*(d+2) : Nat):ℤ) := by exact_mod_cast edges
    push_cast [Nat.cast_sub comp] at h
    exact h
  change Nonempty (ThresholdFourThirds.Regular (n:ℤ) ((B.size:ℤ)-2*(n:ℤ)))
  refine ⟨⟨a,v,c,d,by positivity,by positivity,?_,?_,?_,castEdges,?_⟩⟩
  · omega
  · omega
  · dsimp only [d]; omega
  · exact_mod_cast comp

#print axioms regular_ledger
end ThresholdGlobalGlue
