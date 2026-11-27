import ExactPlanePeriodBranch
import ExactPlanePeriodChoice
import ExactPlaneSuppliedPeriods
namespace ExactPlaneRawPeriod
open ExactPlaneProfileSolver (Selectors rank rank_eq polynomials)
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneProfileCharts (X table)
open ExactPlaneObservedSpan ExactPlanePhysicalConverse ExactPlaneResidualPivots
variable {N d r a : Nat}

def solve (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane) :=
  ExactPlaneEagerSelector.selectBasis
    (ExactPlanePeriodChoice.charts p (rank p-r) (ExactPlaneSuppliedPeriods.codim v)) p b h

theorem solve_iff (v : Fin a→X d) (s : Selectors d r N) (p : Fin N→Key d) (b h : Fin N→Plane)
    (sec : ExactPlaneRawSectionCheck.valid p b s=true) (per : ExactPlaneSuppliedPeriods.valid s h v=true) :
    solve v s p b h≠none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  classical
  unfold solve
  rw [ExactPlaneEagerSelector.selectBasis_eq]
  constructor
  · intro yes
    by_contra! no
    exact yes ((ExactPlaneGaussianSelector.supplied_none _ _ _ _).mpr (fun q _=>no _))
  · rintro ⟨A,tr⟩ no
    obtain ⟨x,hx,ok⟩ := ExactPlanePeriodBranch.sampled_periods p b h (polynomials s h)
      (ExactPlaneRawSectionAdapter.sections_of_valid h sec) (ExactPlaneSuppliedPeriods.W v)
      (ExactPlaneSuppliedPeriods.invariant per) A tr
    apply (ExactPlaneGaussianSelector.supplied_none _ _ _ _).mp no (table p x) _ ok
    refine List.mem_map.mpr ⟨x,?_,rfl⟩
    simpa only [rank_eq,ExactPlaneSuppliedPeriods.codim_eq] using hx

theorem returned {v : Fin a→X d} {s : Selectors d r N} {p : Fin N→Key d} {b h q : Fin N→Plane}
    {B : Finset (Fin N)} (ret : solve v s p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (w : Fin N→Plane) i=>w i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  let cs := ExactPlanePeriodChoice.charts p (rank p-r) (ExactPlaneSuppliedPeriods.codim v)
  change ExactPlaneEagerSelector.selectBasis cs p b h=some (q,B) at ret
  rw [ExactPlaneEagerSelector.selectBasis_eq] at ret
  cases hit : ExactPlaneGaussianSelector.selectCharts cs p b h with
  | none => simp [ExactPlaneGaussianSelector.selectBasis,hit] at ret
  | some pair =>
    obtain ⟨y,A⟩ := pair
    obtain ⟨T,eq,sub,span,yes,count⟩ := ExactPlaneGaussianSelector.supplied_basis hit
    rw [ret] at eq
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj eq)
    obtain ⟨_,_,_,_,same,_⟩ := ExactPlaneGaussianSelector.first_success hit
    exact same ▸ ⟨sub,span,yes,count⟩
#print axioms solve_iff
end ExactPlaneRawPeriod
