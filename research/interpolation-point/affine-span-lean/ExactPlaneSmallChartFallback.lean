import ExactPlaneDeficitSolver
namespace ExactPlaneSmallChartFallback
open ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneObservedSpan ExactPlaneGeneratedDecision
variable {d N : ℕ}

def allRows (d : ℕ) : List (Row d) :=
  (ExactPlaneIrreducibleSearch.words (d+d)).map coordinate

theorem allRows_length (d : ℕ) : (allRows d).length=2^(d+d) := by
  simp [allRows,ExactPlaneIrreducibleSearch.words_length]

theorem mem_allRows (r : Row d) : r∈allRows d := by
  obtain ⟨x,h⟩ := onto d r
  exact List.mem_map.mpr ⟨x,ExactPlaneIrreducibleSearch.mem_words x,h⟩

private theorem sum_realized (p : Fin N→Key d) (src : List (Row d))
    (m : List (Fin N→Plane)) (inside : ∀ a∈m,a∈tables src p) :
    ∃ r : Row d, (fun i=>value r (p i))=m.sum := by
  induction m with
  | nil => exact ⟨0,by funext i; simp [value]⟩
  | cons a m ih =>
    obtain ⟨r,_,rfl⟩ := List.mem_map.mp (inside a (by simp))
    obtain ⟨t,ht⟩ := ih (fun a ha=>inside a (by simp [ha]))
    refine ⟨r+t,?_⟩
    rw [List.sum_cons,←ht]
    funext i
    simp only [Pi.add_apply,value]
    change (∑ j, p i j • ((r (j,false), r (j,true))+(t (j,false),t (j,true))))=_
    simp only [smul_add,Finset.sum_add_distrib]

private theorem contained (rows : List (Row d)) (p : Fin N→Key d) (q : Fin N→Plane)
    (hq : q∈ExactPlaneOddChartList.candidates (tables rows p)) : q∈tables (allRows d) p := by
  obtain ⟨m,inside,_,rfl⟩ := (ExactPlaneOddChartList.mem_candidates _ _).mp hq
  obtain ⟨r,hr⟩ := sum_realized p rows m inside
  exact List.mem_map.mpr ⟨r,mem_allRows r,hr⟩

def direct (p : Fin N→Key d) (b h : Fin N→Plane) :=
  ExactPlaneEagerSelector.selectBasis (tables (allRows d) p) p b h

private theorem direct_witness {p : Fin N→Key d} {b h q : Fin N→Plane} {B : Finset (Fin N)}
    (ret : direct p b h = some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (g : Fin N→Plane) i=>g i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  let charts := tables (allRows d) p
  rw [direct,ExactPlaneEagerSelector.selectBasis_eq] at ret
  cases g : ExactPlaneGaussianSelector.selectCharts charts p b h with
  | none =>
    change (ExactPlaneGaussianSelector.selectCharts charts p b h).map _=some _ at ret
    simp [g] at ret
  | some pair =>
    obtain ⟨y,A⟩ := pair
    obtain ⟨T,c,sub,span,ok,count⟩ := ExactPlaneGaussianSelector.supplied_basis g
    rw [ret] at c
    obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj c)
    obtain ⟨_,_,_,_,id,_⟩ := ExactPlaneGaussianSelector.first_success g
    exact id ▸ ⟨sub,span,ok,count⟩

theorem direct_iff (p : Fin N→Key d) (b h : Fin N→Plane) :
    direct p b h ≠ none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  constructor
  · intro yes
    cases ret : direct p b h with
    | none => exact False.elim (yes ret)
    | some pair =>
      obtain ⟨q,B⟩ := pair
      exact ⟨B,(direct_witness ret).2.2.1⟩
  · intro yes no
    have impossible := (ExactPlaneGeneratedDecision.decide_iff p b h).2 yes
    apply impossible
    let rows := siteRows d (2*(d+2)+1)
    change ExactPlaneEagerSelector.runBasis (tables rows p) p b h=none
    rw [ExactPlaneEagerSelector.runBasis_eq,ExactPlaneGaussianSelector.runBasis,
      ExactPlaneGaussianSelector.supplied_none]
    rw [direct,ExactPlaneEagerSelector.selectBasis_eq,ExactPlaneGaussianSelector.supplied_none] at no
    exact fun q hq=>no q (contained rows p q hq)

def preferAll (d R : ℕ) : Bool :=
  decide (2^(d+d) ≤ (2^(ExactPlaneConstructedRows.exponent (d+d) R))^2)

def solve (p : Fin N→Key d) (b h : Fin N→Plane) :=
  if preferAll d (2*(ExactPlaneComputedDeficit.computed p b+2)+1)
  then direct p b h else ExactPlaneDeficitSolver.solve p b h

theorem solve_iff (p : Fin N→Key d) (b h : Fin N→Plane) :
    solve p b h ≠ none ↔ ∃ A : Finset (Fin N), ExactTrace p b h A := by
  unfold solve
  split
  · exact direct_iff p b h
  · exact ExactPlaneDeficitSolver.solve_iff p b h

theorem witness {p : Fin N→Key d} {b h q : Fin N→Plane} {B : Finset (Fin N)}
    (ret : solve p b h=some (q,B)) :
    let A := ExactPlaneExecutableSelector.accept (fun (g : Fin N→Plane) i=>g i) b q
    B⊆A ∧ physicalSpan p b h B=physicalSpan p b h A ∧ ExactTrace p b h B ∧
      B.card≤Module.finrank (ZMod 2) (observed p)+2 := by
  unfold solve at ret
  split at ret
  · exact direct_witness ret
  · exact ExactPlaneDeficitSolver.witness ret

#print axioms solve_iff
#print axioms witness
end ExactPlaneSmallChartFallback
