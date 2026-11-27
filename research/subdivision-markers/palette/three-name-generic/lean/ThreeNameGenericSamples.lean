import ThreeNameGenericDirect

namespace ThreeNameGenericSamples
open ThreeNameGenericPositive ThreeNameGenericDirect ThreeNamePinReduction ThreeNamePacked

/-- SHA-256 of the respective adjacent samples/*.json raw inputs. The
JSON contents are UTF-8, sorted-key compact, with no trailing newline. -/
def positiveInputSHA256 : String := "feb6f1db2ffddcaab37df0439282c7f0458718dddc195ac9c87b29e90f8050fb"
def conflictInputSHA256 : String := "d701e8d81dbf263083e4530f126adf2fc6c49243e7dae5ecb429feb113d72cd5"
def outsideInputSHA256 : String := "3e5814f0920d11bc76663870e6e34abb3e832ec0ec9410ecf6c9737b399fb644"

/-- IDs 1 and 3 have equal words. The supplied witness uses 3. -/
def sharedCols (i : Fin 5) : BitVec 5 := ([3,11,9,11,4] : List (BitVec 5)).getD i.val 0
theorem positiveCheck :
    check sharedCols [0] [2,3] 1 7 19 [0,2,3] [2] [4] = true := by decide
theorem positiveExact :
    Exact (fun i => decode (sharedCols i)) (named 1 7 19) ({0,2,3} : Finset (Fin 5)) := by
  have h := (sound sharedCols [0] [2,3] 1 7 19 [0,2,3] [2] [4] positiveCheck).2
  exact (show support ([0] : List (Fin 5)) [2,3] = {0,2,3} by decide) ▸ h

/-- The new pin at 4 and the original pin at 0 XOR to forbidden named word 7. -/
theorem conflictCheck :
    checkConflict sharedCols [0,4] 1 7 19 true false false [0,4] = true := by decide
theorem conflictExactNo (A : Finset (Fin 5)) (pins : ([0,4] : List (Fin 5)).toFinset ⊆ A) :
    ¬ Exact (fun i => decode (sharedCols i)) (named 1 7 19) A :=
  conflict_no sharedCols [0,4] 1 7 19 true false false [0,4] conflictCheck A pins

def outsideCols (i : Fin 3) : BitVec 5 := ([2,6,20] : List (BitVec 5)).getD i.val 0
theorem outsideCheck : checkOutside outsideCols 1 [0] = true := by decide
theorem outsideExactNo (A : Finset (Fin 3)) :
    ¬ Exact (fun i => decode (outsideCols i)) (named 1 2 4) A :=
  outside_no outsideCols 1 2 4 [0] outsideCheck A

#print axioms positiveExact
#print axioms conflictExactNo
#print axioms outsideExactNo
end ThreeNameGenericSamples
