import ExactPlaneRawSectionCheck
namespace ExactPlaneSparseProfileExamples
open ExactPlaneSparseANF ExactPlaneSparseProfile ExactPlaneSparseSections ExactPlaneRawSectionCheck
open ExactPlaneAffineSubstitution ExactPlaneSuppliedCoordinates

/-- The same quartic appears in both determinant summands and cancels. -/
private def pairRows (j : Fin 2) : ExactPlaneSparseProfile.Row (Fin 4) :=
  if j=0 then (normalize [[0],[0,2]],normalize [[0,2]])
  else (normalize [[1,3]],normalize [[1,3]])

private def p : Fin 4→Key 1 := fun _ _=>1
private def b : Fin 4→F×F := ![(0,0),(1,0),(0,1),(1,1)]
private def h (i : Fin 4) : F×F := if i=3 then (1,0) else (0,0)
private def sel : Weights 1 4 1 := fun _ i=>
  let a := variableAt (d:=1) 0
  let c := variableAt (d:=1) 1
  times (if (b i).1=1 then a else plus {∅} a)
        (if (b i).2=1 then c else plus {∅} c)
private def broken : Weights 1 4 1 := fun _ _=>{∅}

#eval (actual (augmented pairRows),valid p b sel,actualD sel h,valid p b broken)
example : actual (augmented pairRows)=3 ∧ valid p b sel=true ∧ actualD sel h=2 ∧ valid p b broken=false := by
  native_decide
end ExactPlaneSparseProfileExamples
