import ExactPlaneChargedScan
import ExactPlaneEagerCounts
import ExactPlaneSuppliedCoordinates
namespace ExactPlaneChargedSites
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneResidualPivots (Plane)
variable {d N : Nat}
abbrev Table (N : Nat) := Fin N→Plane

def testSites (q b : Table N) : List (Fin N) → Finset (Fin N) × Nat
  | [] => (∅,0)
  | i::is =>
    let tail := testSites q b is
    (if b i=q i then insert i tail.1 else tail.1,tail.2+1)

theorem test_eq (q b : Table N) (xs : List (Fin N)) :
    testSites q b xs=(xs.toFinset.filter (fun i=>b i=q i),xs.length) := by
  induction xs with
  | nil => simp [testSites]
  | cons a l ih =>
    by_cases h : b a=q a <;> simp [testSites,ih,h,Finset.filter_insert]

def prepare (b q : Table N) := testSites q b (List.finRange N)

theorem prepare_eq (b q : Table N) :
    prepare b q=(ExactPlaneExecutableSelector.accept (fun (z : Table N) i=>z i) b q,N) := by
  simp [prepare,test_eq,ExactPlaneExecutableSelector.accept]

def check (p : Fin N→Key d) (b h : Table N) (A : Finset (Fin N)) :=
  ExactPlaneEagerCounts.checkC (A.sort (·≤·)) p b h

def basis (p : Fin N→Key d) (b h : Table N) (A : Finset (Fin N)) :=
  ExactPlaneEagerCounts.basisC A p b h

def run (cs : List (Table N)) (p : Fin N→Key d) (b h : Table N) :=
  ExactPlaneChargedScan.scan (prepare b) (check p b h) (basis p b h) cs

theorem answer_eq (cs : List (Table N)) (p : Fin N→Key d) (b h : Table N) :
    (run cs p b h).answer=ExactPlaneEagerSelector.selectBasis cs p b h := by
  rw [run,ExactPlaneChargedScan.answer_eq]
  have cp : (fun A=>(check p b h A).1)=ExactPlaneEagerSelector.valid p b h :=
    funext fun A=>(ExactPlaneEagerCounts.checkC_spec (A.sort (·≤·)) p b h).1
  simp only [prepare_eq,cp,ExactPlaneEagerSelector.selectBasis,ExactPlaneEagerSelector.selectCharts,
    basis,fun A=>(ExactPlaneEagerCounts.basisC_spec A p b h).1]

theorem counts (cs : List (Table N)) (p : Fin N→Key d) (b h : Table N) :
    let o := run cs p b h
    o.tested≤cs.length ∧ o.siteTests=o.tested*N ∧ o.checkPivots≤o.tested*((N+5)*(d+4)) ∧
      o.recovered=(if o.answer.isSome then 1 else 0) ∧ o.basisPivots≤o.recovered*(2*N*(d+4)) := by
  apply ExactPlaneChargedScan.counts
  · intro q; rw [prepare_eq]
  · intro A
    have size := Finset.card_le_univ A
    simp only [Fintype.card_fin] at size
    have cost := (ExactPlaneEagerCounts.checkC_spec (A.sort (·≤·)) p b h).2
    rw [Finset.length_sort] at cost
    exact cost.trans (Nat.mul_le_mul_right _ (Nat.add_le_add_right size _))
  · intro A
    have size := Finset.card_le_univ A
    simp only [Fintype.card_fin] at size
    exact (ExactPlaneEagerCounts.basisC_spec A p b h).2.trans
      (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2 size))
end ExactPlaneChargedSites
