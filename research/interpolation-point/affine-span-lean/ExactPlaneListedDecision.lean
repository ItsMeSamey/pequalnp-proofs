import ExactPlaneExecutableSelector
import ExactPlaneOddChartList
import ExactPlaneRawApplication
namespace ExactPlaneExecutableSelector
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
open ExactPlaneGlobalApplication ExactPlaneOddChartList
variable {K : Type*} [AddCommGroup K] [Module F K] [DecidableEq K] {N : ℕ}

def run (seed : List (Fin N→Plane)) (priv : Fin N→K) (tag height : Fin N→Plane) :=
  select (fun q i=>q i) priv tag height (candidates seed)

theorem run_some {seed : List (Fin N→Plane)} {priv : Fin N→K} {tag height : Fin N→Plane}
    {q : Fin N→Plane} {A : Finset (Fin N)} (yes : run seed priv tag height=some (q,A)) :
    A=accept (fun g i=>g i) tag q ∧ ExactTrace priv tag height A := by
  obtain ⟨_,_,_,_,ids,good⟩ := select_some yes
  exact ⟨ids,good⟩

theorem exists_complete_seed (priv : Fin N→K) (tag : Fin N→Plane) :
    let R := 2*(ExactPlaneFullDirections.deficit F (key priv) tag+2)+1
    ∃ seed : List (Fin N→Plane),seed.length≤max 1 ((2*(Module.finrank F (observed priv)*2)*2^R)^2) ∧
      ∀ height : Fin N→Plane,
        run seed priv tag height≠none ↔ ∃ A : Finset (Fin N),ExactTrace priv tag height A := by
  classical
  intro R
  obtain ⟨S,cap,spec⟩ := raw_decision_iff priv tag
  let table := fun (g : observed priv→ₗ[F] Plane) (i : Fin N)=>g (key priv i)
  let seeds := S.toList.map table
  refine ⟨seeds,by simpa [seeds] using cap,?_⟩
  intro height
  constructor
  · intro yes
    cases h : run seeds priv tag height with
    | none => exact False.elim (yes h)
    | some ans => exact ⟨ans.2,(run_some (q:=ans.1) (A:=ans.2) h).2⟩
  · intro yes no
    obtain ⟨m,inside,len,t⟩ := (spec height).mp yes
    have mem : (m.map table).sum∈candidates seeds := by
      apply (mem_candidates _ _).mpr
      refine ⟨m.map table,?_,by simpa using len,rfl⟩
      intro x h
      obtain ⟨g,hg,rfl⟩ := List.mem_map.mp h
      exact List.mem_map.mpr ⟨g,by simpa using inside g hg,rfl⟩
    have evaluated : (m.map table).sum=table m.sum := by
      clear inside len t mem
      induction m with
      | nil => rfl
      | cons g m ih => simp only [List.map_cons,List.sum_cons,ih]; rfl
    have noTrace := (select_none (fun (q : Fin N→Plane) i=>q i) priv tag height (candidates seeds)).mp no _ mem
    rw [evaluated] at noTrace
    exact noTrace t.1
#print axioms exists_complete_seed
end ExactPlaneExecutableSelector
