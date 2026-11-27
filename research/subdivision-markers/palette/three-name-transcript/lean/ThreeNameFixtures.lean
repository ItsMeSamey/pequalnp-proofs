import Init

namespace ThreeNameFixtures

/-- Enumerate all binary sums of already selected columns. -/
def search (pins : List Nat) (i : Nat) (span : List Nat) : List Nat → Bool
  | [] => span.contains 1 && !(span.any (fun v => 2 ≤ v && v ≤ 7))
  | x :: xs =>
    let take := fun _ : Unit => search pins (i+1) (span ++ span.map (fun v => v ^^^ x)) xs
    if pins.contains i then take () else search pins (i+1) span xs || take ()

def physical (columns pins : List Nat) := search pins 0 [0] columns

set_option maxRecDepth 20000
set_option maxHeartbeats 4000000

theorem star_fixture : physical [2, 3, 8, 10, 12, 16, 18, 32] [] = false := by decide

theorem excluded_fixture : physical [8, 9] [] = true := by decide

theorem pins_witness_fixture : physical [0, 1, 1] [2] = true := by decide

theorem pins_conflict_fixture : physical [3, 2] [0] = false := by decide

theorem outside_fixture : physical [2] [] = false := by decide

theorem single_fixture : physical [0, 1] [] = true := by decide

end ThreeNameFixtures
