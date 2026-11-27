import ExactPlaneChargedOdd
import ExactPlaneChargedGenerator
import ExactPlaneChargedSites
import ExactPlaneDeficitCharged
import ExactPlaneDeficitSolver
namespace ExactPlaneChargedSolver
open ExactPlaneSuppliedCoordinates (Key tables)
open ExactPlaneChargedSites (Table)
variable {N d : ℕ}
structure FieldCounts where
  modulusCandidates : Nat
  divisions : Nat
  fieldMuls : Nat
  dotEntries : Nat
  baseTables : Nat
  seedRows : Nat

structure Output (N : Nat) where
  deficit : ExactPlaneDeficitCharged.Result
  field : FieldCounts
  emitted : Nat
  terms : Nat
  search : ExactPlaneChargedScan.Output (Table N) (Fin N)

def budget (t : Nat) := 2*(t+2)+1
def seedSize (m R : Nat) := if m=0 then 1 else (ExactPlaneChargedGenerator.q m R)^2

def run (p : Fin N→Key d) (b h : Table N) : Output N :=
  let pre := ExactPlaneDeficitCharged.run p b
  let g := ExactPlaneChargedGenerator.run (d+d) (budget pre.value)
  let base := (ExactPlaneNumericalRows.points g.rows).map ExactPlaneGeneratedDecision.coordinate
  let odd := ExactPlaneChargedOdd.counted (tables base p)
  let scan := ExactPlaneChargedSites.run odd.charts p b h
  ⟨pre,⟨g.modulusCandidates,g.divisions,g.fieldMuls,g.dotEntries,g.baseTables,g.rows.length⟩,
    odd.emitted,odd.terms,scan⟩

theorem answer (p : Fin N→Key d) (b h : Table N) :
    (run p b h).search.answer = ExactPlaneDeficitSolver.solve p b h := by
  simp only [run,ExactPlaneChargedSites.answer_eq,ExactPlaneChargedOdd.counted_spec,
    ExactPlaneChargedGenerator.rows_eq,(ExactPlaneDeficitCharged.run_spec p b).1]
  rfl

theorem preprocess (p : Fin N→Key d) (b h : Table N) :
    let o := (run p b h).deficit
    o.value=ExactPlaneComputedDeficit.computed p b ∧ o.scan.keyBits=N^2*d ∧
      o.scan.tagPairs≤4*N^2 ∧ o.scan.keyBits+2*o.scan.tagPairs≤N^2*(d+8) ∧
      o.scan.firstRankSites=N ∧ o.scan.secondRankSites≤N ∧ o.visits≤4*N*(d+4) := by
  obtain ⟨v,s,count⟩ := ExactPlaneDeficitCharged.run_spec p b
  obtain ⟨a,c,e,i,j⟩ := ExactPlaneDeficitScan.counts_bound p b
  simpa only [run,s] using And.intro v (And.intro a (And.intro c (And.intro e (And.intro i (And.intro j count)))))

theorem field (p : Fin N→Key d) (b h : Table N) :
    let o := run p b h
    let m := d+d
    let R := budget o.deficit.value
    let q := ExactPlaneChargedGenerator.q m R
    let e := ExactPlaneConstructedRows.exponent m R
    o.field.modulusCandidates≤q ∧ o.field.divisions≤o.field.modulusCandidates*(2^(e/2+1)-2) ∧
      o.field.fieldMuls=q*m ∧ o.field.dotEntries=q^2*m ∧ o.field.baseTables=q ∧
      o.field.seedRows=seedSize m R := by
  exact ExactPlaneChargedGenerator.counts _ _

theorem enumeration (p : Fin N→Key d) (b h : Table N) :
    let o := run p b h
    o.emitted=ExactPlaneChargedOdd.card o.field.seedRows ∧ o.terms=ExactPlaneChargedOdd.occurrences o.field.seedRows := by
  simp only [run,ExactPlaneChargedOdd.counted_spec,tables,List.length_map,ExactPlaneNumericalRows.points,true_and]

theorem traversal (p : Fin N→Key d) (b h : Table N) :
    let o := run p b h
    o.search.tested≤o.emitted ∧ o.search.siteTests=o.search.tested*N ∧
      o.search.checkPivots≤o.search.tested*((N+5)*(d+4)) ∧
      o.search.recovered=(if o.search.answer.isSome then 1 else 0) ∧
      o.search.basisPivots≤o.search.recovered*(2*N*(d+4)) := by
  let pre := ExactPlaneDeficitCharged.run p b
  let g := ExactPlaneChargedGenerator.run (d+d) (budget pre.value)
  let s := tables ((ExactPlaneNumericalRows.points g.rows).map ExactPlaneGeneratedDecision.coordinate) p
  simpa only [run,ExactPlaneChargedOdd.counted_spec,ExactPlaneOddChartList.count_candidates,ExactPlaneChargedOdd.card,
    s,g,pre] using ExactPlaneChargedSites.counts (ExactPlaneOddChartList.candidates s) p b h

#print axioms answer
#print axioms traversal
end ExactPlaneChargedSolver
