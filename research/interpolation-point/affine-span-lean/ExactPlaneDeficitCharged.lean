import ExactPlaneDeficitScan
import ExactPlaneEagerCounts
namespace ExactPlaneDeficitCharged
open ExactPlaneSuppliedCoordinates ExactPlaneResidualPivots
variable {d N : ℕ}

structure Result where
  value : ℕ
  scan : ExactPlaneDeficitScan.Counts
  visits : ℕ
  deriving Repr

def run (p : Fin N→Key d) (b : Fin N→Plane) : Result :=
  let raw := ExactPlaneDeficitScan.inspect p b
  let first := ExactPlaneEagerCounts.basisC Finset.univ p 0 0
  let second := ExactPlaneEagerCounts.basisC raw.1 p 0 0
  ⟨first.1.card-second.1.card,raw.2,first.2+second.2⟩

theorem run_spec (p : Fin N→Key d) (b : Fin N→Plane) :
    let z := run p b
    z.value=ExactPlaneComputedDeficit.computed p b ∧ z.scan=ExactPlaneDeficitScan.counts p b ∧
      z.visits≤4*N*(d+4) := by
  obtain ⟨f,hf⟩ := ExactPlaneEagerCounts.basisC_spec Finset.univ p 0 0
  obtain ⟨s,hs⟩ := ExactPlaneEagerCounts.basisC_spec (ExactPlaneDeficitScan.accepted p b) p 0 0
  change _ ∧ _ ∧ _
  simp only [run,ExactPlaneDeficitScan.inspect_eq,Prod.fst,Prod.snd,f,s,true_and]
  constructor
  · rw [←ExactPlaneDeficitScan.computed_eq]
    rfl
  · have card : (ExactPlaneDeficitScan.accepted p b).card ≤ N :=
      (Finset.card_le_univ _).trans_eq (Fintype.card_fin N)
    simp only [Finset.card_univ,Fintype.card_fin] at hf
    calc
      _ ≤ _ := Nat.add_le_add hf hs
      _ ≤ 2*N*(d+4) + 2*N*(d+4) := by gcongr
      _ = _ := by ring

#print axioms run_spec
end ExactPlaneDeficitCharged
