import ExactPlaneEagerBank
namespace ExactPlaneEagerSelector
open ExactPlaneExecutableSelector ExactPlaneResidualPivots ExactPlanePhysicalConverse ExactPlaneObservedSpan
variable {d N : ℕ}
abbrev Key := ExactPlaneGaussianSelector.Key
abbrev Table := ExactPlaneGaussianSelector.Table

def valid (priv : Fin N→Key d) (tag height : Table N) (A : Finset (Fin N)) :=
  ExactPlaneEagerBank.check (A.sort (·≤·)) priv tag height

def selectCharts (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  scan (accept (fun q i=>q i) tag) (valid priv tag height) charts

theorem selectCharts_eq (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    selectCharts charts priv tag height=ExactPlaneGaussianSelector.selectCharts charts priv tag height := by
  have h : valid priv tag height=ExactPlaneGaussianSelector.valid priv tag height :=
    funext fun A=>ExactPlaneEagerBank.check_eq (A.sort (·≤·)) priv tag height
  unfold selectCharts ExactPlaneGaussianSelector.selectCharts
  rw [h]

def selectBasis (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  (selectCharts charts priv tag height).map fun result =>
    (result.1,ExactPlaneEagerBank.basis result.2 priv tag height)

theorem selectBasis_eq (charts : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    selectBasis charts priv tag height=ExactPlaneGaussianSelector.selectBasis charts priv tag height := by
  simp only [selectBasis, ExactPlaneGaussianSelector.selectBasis, selectCharts_eq, ExactPlaneEagerBank.basis_eq]

def runBasis (seed : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :=
  selectBasis (ExactPlaneOddChartList.candidates seed) priv tag height

theorem runBasis_eq (seed : List (Table N)) (priv : Fin N→Key d) (tag height : Table N) :
    runBasis seed priv tag height=ExactPlaneGaussianSelector.runBasis seed priv tag height :=
  selectBasis_eq _ _ _ _

/-- Array-backed physical keys, seed charts, tags and heights. -/
def runPacked (seeds : List (Vector Plane N)) (keys : Vector (Vector F d) N)
    (tags heights : Vector Plane N) : Option (Vector Plane N × Finset (Fin N)) :=
  (runBasis (seeds.map fun row i=>row[i]) (fun i j=>keys[i][j]) (fun i=>tags[i]) (fun i=>heights[i])).map
    fun result => (Vector.ofFn result.1,result.2)

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
  simpa only [runBasis_eq] using ExactPlaneGaussianSelector.decide_with_basis priv tag
#print axioms decide_with_basis
end ExactPlaneEagerSelector
