import ExactPlaneRawPeriod
namespace ExactPlaneCheckedPeriod
open ExactPlaneProfileSolver (Selectors rank)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneProfileCharts (X)
open ExactPlanePhysicalConverse ExactPlaneObservedSpan ExactPlaneResidualPivots
variable {N d r a : Nat}

def usePeriod (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (h : Fin N→Plane) :=
  ExactPlanePeriodChoice.preferPeriod (d+d) (rank p-r) (ExactPlaneSparseSections.actualD s h)
    (ExactPlaneSuppliedPeriods.codim v)

def solve (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :=
  if ExactPlaneRawSectionCheck.valid p b s then
    if ExactPlaneSuppliedPeriods.valid s h v && usePeriod v s p h then ExactPlaneRawPeriod.solve v s p b h
    else ExactPlaneProfileSolver.solve s p b h
  else ExactPlaneDeficitSolver.solve p b h

theorem solve_iff (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :
    solve v s p b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  unfold solve
  split
  next sec =>
    split
    next both => exact ExactPlaneRawPeriod.solve_iff v s p b h sec (Bool.and_eq_true_iff.mp both).1
    next => exact ExactPlaneProfileSolver.solve_iff s p b h (ExactPlaneRawSectionAdapter.sections_of_valid h sec)
  next => exact ExactPlaneDeficitSolver.solve_iff p b h

theorem returned {v : Fin a→X d} {s : Selectors d r N} {p : Fin N→Key d} {b h q : Fin N→Plane}
    {B : Finset (Fin N)} (ret : solve v s p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (z : Fin N→Plane) i=>z i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  unfold solve at ret
  split at ret
  · split at ret
    · exact ExactPlaneRawPeriod.returned ret
    · exact ExactPlaneProfileSolver.witness ret
  · exact ExactPlaneDeficitSolver.witness ret

theorem valid_path {v : Fin a→X d} {s : Selectors d r N} {p : Fin N→Key d} {b h : Fin N→Plane}
    (sec : ExactPlaneRawSectionCheck.valid p b s=true) (per : ExactPlaneSuppliedPeriods.valid s h v=true) :
    solve v s p b h =
      if usePeriod v s p h then ExactPlaneRawPeriod.solve v s p b h
      else ExactPlaneProfileSolver.solve s p b h := by simp [solve,sec,per]

theorem candidate_count (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (h : Fin N→Plane) :
    let t := rank p-r
    let c := ExactPlaneSuppliedPeriods.codim v
    let D := ExactPlaneSparseSections.actualD s h
    (if usePeriod v s p h then (ExactPlanePeriodChoice.charts p t c).length
      else (ExactPlaneProfileSolver.charts s p h).length) =
      min (ExactPlanePeriodChoice.periodCount (d+d) t c) (ExactPlanePeriodChoice.degreeCount (d+d) t D) := by
  simpa only [usePeriod,ExactPlanePeriodChoice.period_count,ExactPlanePeriodChoice.degree_count] using
    ExactPlanePeriodChoice.fewer (d+d) (rank p-r) (ExactPlaneSparseSections.actualD s h) (ExactPlaneSuppliedPeriods.codim v)
#print axioms solve_iff
#print axioms returned
#print axioms candidate_count
end ExactPlaneCheckedPeriod
