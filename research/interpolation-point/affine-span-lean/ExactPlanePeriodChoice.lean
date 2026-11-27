import ExactPlaneCheckedProfile
namespace ExactPlanePeriodChoice
open ExactPlaneProfileSolver (Selectors)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneResidualPivots (Plane)
variable {r d N : Nat}

def seedCount (m R : Nat) := if m=0 then 1 else (2^(ExactPlaneConstructedRows.exponent m R))^2

theorem seed_count (m R : Nat) : (ExactPlaneConstructedRows.generate m R).length=seedCount m R := by
  cases m with
  | zero => rfl
  | succ m => rw [ExactPlaneConstructedRows.generate,ExactPlaneEagerField.seedRows_eq,ExactPlaneQuotientRows.count]
              simp [seedCount]

def degreeCount (m t D : Nat) :=
  ((List.range (D/2+1)).map (fun j=>(seedCount m (2*(t+2)+1))^(2*j+1))).sum

def periodCount (m t c : Nat) := seedCount m (c+2*(t+2))

theorem degree_count (s : Selectors d r N) (p : Fin N→Key d) (h : Fin N→Plane) :
    (ExactPlaneProfileSolver.charts s p h).length=degreeCount (d+d) (ExactPlaneProfileSolver.rank p-r)
      (ExactPlaneSparseSections.actualD s h) := by
  simpa only [degreeCount,seed_count] using ExactPlaneCheckedProfile.chart_count s p h

def charts (p : Fin N→Key d) (t c : Nat) :=
  (ExactPlaneNumericalRows.points (ExactPlaneConstructedRows.generate (d+d) (c+2*(t+2)))).map
    (ExactPlaneProfileCharts.table p)

theorem period_count (p : Fin N→Key d) (t c : Nat) :
    (charts p t c).length=periodCount (d+d) t c := by
  simp only [charts,ExactPlaneNumericalRows.points,List.length_map,seed_count,periodCount]

/-- The tie is resolved in favor of a single-seed scan. No chart list is built to compare the counts. -/
def preferPeriod (m t D c : Nat) : Bool := decide (periodCount m t c ≤ degreeCount m t D)

theorem fewer (m t D c : Nat) :
    (if preferPeriod m t D c then periodCount m t c else degreeCount m t D)=
      min (periodCount m t c) (degreeCount m t D) := by
  by_cases h : periodCount m t c≤degreeCount m t D
  · simp [preferPeriod,h,min_eq_left h]
  · simp [preferPeriod,h,min_eq_right (le_of_not_ge h)]
end ExactPlanePeriodChoice
