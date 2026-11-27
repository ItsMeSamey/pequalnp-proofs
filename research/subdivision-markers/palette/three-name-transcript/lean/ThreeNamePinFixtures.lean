import ThreeNamePackedPins

namespace ThreeNamePinFixtures
open ThreeNamePackedPins ThreeNamePacked ThreeNamePinReduction ExactPlaneGaussian

def table : Table 4 := [(1,3)]
/-- Positions 1 and 2 are distinct equal columns; return 2 and retain pin 0. -/
def col (i : Fin 3) : BitVec 4 := if i = 0 then 3 else 2

theorem checked : check col [0] table (fun _ => [0]) = true := by decide

theorem python_word : run table 1 = 1 := by decide

theorem first_pivot_word :
    project (fun i => ThreeNamePacked.decode (col i)) [0] (ThreeNamePacked.decode (1 : BitVec 4)) =
      ThreeNamePacked.decode (2 : BitVec 4) := by
  funext j
  fin_cases j <;> decide

/-- t,a,b are 1,6,8. Include all three labelled pair sums and a
nontrivial interface triple (2,6,4). -/
theorem raw_roots_and_interface :
    ([6,8,15,14,7,9] : List (BitVec 4)).map (run table) = [5,8,12,13,4,9] ∧
    ([2,6,4] : List (BitVec 4)).map (run table) = [1,5,4] := by decide

/-- The named words are listed by axis bit first, followed by tag bits.
This evaluates the entire trace on the two chosen original positions. -/
def namedWords : List (BitVec 4) := [0,1,6,7,8,9,14,15]

theorem original_id_trace :
    run table (col 2) = 1 ∧ col 0 ^^^ col 2 = 1 ∧
    ({0} : Finset (Fin 3)) ⊆ {0,2} ∧
    ∀ i : Fin 8, (∃ usePin useOrd : Bool,
      (if usePin then col 0 else 0) ^^^ (if useOrd then col 2 else 0) =
        namedWords[i.val]!) ↔ i.val ≤ 1 := by decide

/-- Raw values from the pinned three-split Python transcript regression. -/
theorem transcript_names_and_interfaces :
    ([1,7,11] : List (BitVec 6)).map (run [(1,3)]) = [1,4,8] ∧
    ([[],[4],[4,8]] : List (List (BitVec 6))).map
      (List.map (run [(1,3)])) = [[],[4],[4,8]] := by decide

theorem transcript_yes_support :
    ([3,35,33] : List (BitVec 6)).map (run [(1,3)]) = [0,32,33] ∧
      xorSum ([3,35,33] : List (BitVec 6)) = 1 ∧
      ∀ i : Fin 8, (∃ a b c : Bool,
        (if a then (3 : BitVec 6) else 0) ^^^ (if b then 35 else 0) ^^^ (if c then 33 else 0)
        = ([0,1,7,6,11,10,12,13] : List (BitVec 6))[i.val]!) ↔ i.val ≤ 1 := by decide

#print axioms transcript_yes_support
#print axioms first_pivot_word
#print axioms original_id_trace
end ThreeNamePinFixtures
