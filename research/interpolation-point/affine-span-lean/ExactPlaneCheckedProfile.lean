import ExactPlaneRawSectionAdapter
import ExactPlaneDeficitSolver
namespace ExactPlaneCheckedProfile
open ExactPlaneProfileSolver (Selectors)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlanePhysicalConverse ExactPlaneObservedSpan ExactPlaneResidualPivots
variable {N d r : Nat}

/-- A verified supplied family uses its determinant degree. Other families
fall back to the per-key exact-trace solver. -/
def solve (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :=
  if ExactPlaneRawSectionCheck.valid p b s then ExactPlaneProfileSolver.solve s p b h
  else ExactPlaneDeficitSolver.solve p b h

theorem solve_iff (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :
    solve s p b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  unfold solve
  split
  next ok =>
    exact ExactPlaneProfileSolver.solve_iff s p b h
      (ExactPlaneRawSectionAdapter.sections_of_valid h ok)
  next => exact ExactPlaneDeficitSolver.solve_iff p b h

theorem returned {s : Selectors d r N} {p : Fin N→Key d} {b h q : Fin N→Plane}
    {B : Finset (Fin N)} (found : solve s p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (g : Fin N→Plane) i=>g i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  unfold solve at found
  split at found
  · exact ExactPlaneProfileSolver.witness found
  · exact ExactPlaneDeficitSolver.witness found

theorem valid_path {s : Selectors d r N} {p : Fin N→Key d} {b h : Fin N→Plane}
    (ok : ExactPlaneRawSectionCheck.valid p b s=true) :
    solve s p b h=ExactPlaneProfileSolver.solve s p b h := by simp [solve,ok]

theorem chart_count (s : Selectors d r N) (p : Fin N→Key d) (h : Fin N→Plane) :
    let t := ExactPlaneProfileSolver.rank p-r
    let D := ExactPlaneSparseSections.actualD s h
    let n := (ExactPlaneConstructedRows.generate (d+d) (2*(t+2)+1)).length
    (ExactPlaneProfileSolver.charts s p h).length =
      ((List.range (D/2+1)).map (fun j=>n^(2*j+1))).sum := by
  simp only [ExactPlaneProfileSolver.charts,ExactPlaneDegreeSampler.candidates,List.length_map,
    ExactPlaneDegreeSampler.ordered_count,ExactPlaneNumericalRows.points]

#print axioms chart_count
#print axioms solve_iff
#print axioms returned
end ExactPlaneCheckedProfile
