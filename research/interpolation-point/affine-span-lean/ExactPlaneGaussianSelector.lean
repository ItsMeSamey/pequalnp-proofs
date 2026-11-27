import ExactPlaneGaussianCandidate
import ExactPlaneListedDecision
import Mathlib.Data.Finset.Sort
namespace ExactPlaneGaussianSelector
open ExactPlaneExecutableSelector ExactPlaneOddChartList ExactPlaneResidualPivots ExactPlanePhysicalConverse
variable {d N : ℕ}
abbrev Key (d : ℕ) := Fin d→ZMod 2
abbrev Table (N : ℕ) := Fin N→Plane

def valid (priv : Fin N→Key d) (tag height : Table N) (A : Finset (Fin N)) : Bool :=
  ExactPlaneGaussianCandidate.check (A.sort (·≤·)) priv tag height

theorem valid_iff (priv : Fin N→Key d) (tag height : Table N) (A : Finset (Fin N)) :
    valid priv tag height A=true ↔ ExactTrace priv tag height A := by
  simpa only [valid,Finset.sort_toFinset] using
    ExactPlaneGaussianCandidate.check_iff (A.sort (·≤·)) priv tag height

def selectCharts (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  scan (accept (fun q i=>q i) tag) (valid priv tag height) charts

theorem select_eq (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    selectCharts charts priv tag height =
      select (fun (q : Table N) i=>q i) priv tag height charts := by
  have same : valid priv tag height = (fun A=>ExactPlaneCandidateCheck.check A priv tag height) := by
    funext A
    have eq := (valid_iff priv tag height A).trans (ExactPlaneCandidateCheck.check_iff A priv tag height).symm
    cases h : valid priv tag height A <;> cases j : ExactPlaneCandidateCheck.check A priv tag height <;> simp_all
  unfold selectCharts select
  rw [same]

def run (seed : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  selectCharts (candidates seed) priv tag height

theorem run_eq (seed : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    run seed priv tag height=ExactPlaneExecutableSelector.run seed priv tag height :=
  select_eq _ _ _ _

theorem first_success {charts : List (Table N)} {priv : Fin N→Key d} {tag height : Table N}
    {q : Table N} {A : Finset (Fin N)} (ret : selectCharts charts priv tag height=some (q,A)) :
    ∃ pre post,charts=pre++q::post ∧
      (∀ p∈pre,¬ExactTrace priv tag height (accept (fun g i=>g i) tag p)) ∧
      A=accept (fun g i=>g i) tag q ∧ ExactTrace priv tag height A := by
  rw [select_eq] at ret
  exact select_some ret
#print axioms run_eq
#print axioms first_success
end ExactPlaneGaussianSelector
