import ExactPlaneGaussianSelector
import ExactPlaneGaussianIDs
import ExactPlaneGaussianBasisBound
namespace ExactPlaneGaussianSelector
open ExactPlaneExecutableSelector ExactPlaneResidualPivots ExactPlanePhysicalConverse ExactPlaneObservedSpan
variable {d N : ℕ}

def selectBasis (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  (selectCharts charts priv tag height).map fun result =>
    (result.1,ExactPlaneGaussianIDs.basis result.2 priv tag height)

def runBasis (seed : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  selectBasis (ExactPlaneOddChartList.candidates seed) priv tag height

theorem supplied_none (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    selectBasis charts priv tag height=none ↔
      ∀ q∈charts,¬ExactTrace priv tag height (accept (fun (p : Table N) i=>p i) tag q) := by
  simpa only [selectBasis,Option.map_eq_none_iff,select_eq] using
    (select_none (fun (p : Table N) i=>p i) priv tag height charts)

theorem supplied_basis {charts : List (Table N)} {priv : Fin N→Key d} {tag height : Table N}
    {q : Table N} {A : Finset (Fin N)} (found : selectCharts charts priv tag height=some (q,A)) :
    ∃ B,selectBasis charts priv tag height=some (q,B) ∧ B⊆A ∧
      physicalSpan priv tag height B=physicalSpan priv tag height A ∧ ExactTrace priv tag height B ∧
      B.card≤Module.finrank F (observed priv)+2 := by
  obtain ⟨sub,li,span⟩ := ExactPlaneGaussianIDs.keep_spec A priv tag height
  obtain ⟨_,_,_,_,_,yes⟩ := first_success found
  exact ⟨_,by simp [selectBasis,found],sub,span,ExactPlaneGaussianBasisBound.bound priv tag height A _ yes li span⟩

theorem runBasis_witness {seed : List (Table N)} {priv : Fin N→Key d} {tag height : Table N}
    {q : Table N} {A : Finset (Fin N)}
    (found : ExactPlaneGaussianSelector.run seed priv tag height=some (q,A)) :
    ∃ B,runBasis seed priv tag height=some (q,B) ∧ B⊆A ∧
      physicalSpan priv tag height B=physicalSpan priv tag height A ∧ ExactTrace priv tag height B ∧
      B.card≤Module.finrank F (observed priv)+2 :=
  supplied_basis found

theorem decide_with_basis (priv : Fin N→Key d) (tag : Table N) :
    let R := 2*(ExactPlaneFullDirections.deficit F (key priv) tag+2)+1
    ∃ seed : List (Table N),seed.length≤max 1 ((2*(Module.finrank F (observed priv)*2)*2^R)^2) ∧
      ∀ height : Table N,
        (∃ A : Finset (Fin N), ExactTrace priv tag height A) ↔
          ∃ (q : Table N) (B : Finset (Fin N)),
            runBasis seed priv tag height=some (q,B) ∧
            B⊆accept (fun (p : Table N) i=>p i) tag q ∧
            physicalSpan priv tag height B=physicalSpan priv tag height (accept (fun (p : Table N) i=>p i) tag q) ∧
            ExactTrace priv tag height B ∧ B.card≤Module.finrank F (observed priv)+2 := by
  intro R
  obtain ⟨seed,cap,decision⟩ := exists_complete_seed priv tag
  refine ⟨seed,cap,?_⟩
  intro height
  constructor
  · intro yes
    have pass := (decision height).mpr yes
    rw [←run_eq] at pass
    cases h : ExactPlaneGaussianSelector.run seed priv tag height with
    | none => exact False.elim (pass h)
    | some a =>
      obtain ⟨q,A⟩ := a
      obtain ⟨B,ret,sub,span,ok,bd⟩ := runBasis_witness h
      have ref : ExactPlaneExecutableSelector.run seed priv tag height=some (q,A) := by rwa [←run_eq]
      have id := (run_some ref).1
      exact ⟨q,B,ret,id ▸ sub,id ▸ span,ok,bd⟩
  · rintro ⟨_,B,_,_,_,yes,_⟩
    exact ⟨B,yes⟩
#print axioms runBasis_witness
#print axioms decide_with_basis
end ExactPlaneGaussianSelector
