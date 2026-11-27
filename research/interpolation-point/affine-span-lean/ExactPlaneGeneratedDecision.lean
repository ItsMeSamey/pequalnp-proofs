import ExactPlaneConstructedRows
import ExactPlaneSuppliedCoordinates
namespace ExactPlaneGeneratedDecision
open ExactPlaneFieldSampler ExactPlaneSamplerRank ExactPlaneSuppliedCoordinates
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan ExactPlaneFullDirections
def coordinate (x : V (d+d)) : Row d := fun p=>
  if p.2 then x (Fin.natAdd d p.1) else x (Fin.castAdd d p.1)

def chartMap (d : Nat) : V (d+d) →ₗ[ZMod 2] Row d where
  toFun := coordinate
  map_add' x y := by funext p; cases p with | mk i b => cases b <;> rfl
  map_smul' a x := by funext p; cases p with | mk i b => cases b <;> rfl

theorem onto (d : Nat) : Function.Surjective (chartMap d) := by
  intro y
  refine ⟨Fin.addCases (fun i=>y (i,false)) (fun i=>y (i,true)),?_⟩
  funext p
  rcases p with ⟨i,b⟩
  cases b
  · change Fin.addCases (motive := fun _ : Fin (d+d) => ZMod 2) (fun j=>y (j,false)) (fun j=>y (j,true)) (Fin.castAdd d i)=_
    exact Fin.addCases_left i
  · change Fin.addCases (motive := fun _ : Fin (d+d) => ZMod 2) (fun j=>y (j,false)) (fun j=>y (j,true)) (Fin.natAdd d i)=_
    exact Fin.addCases_right i

def siteRows (d R : Nat) : List (Row d) :=
  (ExactPlaneNumericalRows.points (ExactPlaneConstructedRows.generate (d+d) R)).map coordinate

theorem site_hits (d R : Nat) : OntoHits (siteRows d R).toFinset R := by
  intro k hk f surj y
  obtain ⟨x,hx,val⟩ := ExactPlaneConstructedRows.generate_hits (d+d) R k hk
    (f.comp (chartMap d)) (surj.comp (onto d)) y
  exact ⟨_,List.mem_toFinset.mpr (List.mem_map.mpr ⟨x,List.mem_toFinset.mp hx,rfl⟩),val⟩

def run (R : Nat) (priv : Fin N→Key d) (tag height : Fin N→Plane) :=
  ExactPlaneEagerSelector.runBasis (tables (siteRows d R) priv) priv tag height

theorem decision (R : Nat) (priv : Fin N→Key d) (tag height : Fin N→Plane)
    (enough : 2*(deficit (ZMod 2) (key priv) tag+2)+1 ≤ R) :
    run R priv tag height ≠ none ↔ ∃ A : Finset (Fin N), ExactTrace priv tag height A :=
  supplied_decision _ _ _ _ _ enough (site_hits d R)
def decide (priv : Fin N→Key d) (tag height : Fin N→Plane) :=
  run (2*(d+2)+1) priv tag height

theorem decide_iff (priv : Fin N→Key d) (tag height : Fin N→Plane) :
    decide priv tag height ≠ none ↔ ∃ A : Finset (Fin N), ExactTrace priv tag height A :=
  ambient_decision _ _ _ _ (site_hits d (2*(d+2)+1))

#print axioms decide_iff
#print axioms decision
end ExactPlaneGeneratedDecision
