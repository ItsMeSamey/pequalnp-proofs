import ThreeNameGenericDirect

namespace DirectInstance_feb6f1db2ffddcaab37df0439282c7f0458718dddc195ac9c87b29e90f8050fb
open ThreeNamePacked ThreeNamePinReduction ThreeNameGenericPositive ThreeNameGenericDirect
def rawInputSHA256 : String := "feb6f1db2ffddcaab37df0439282c7f0458718dddc195ac9c87b29e90f8050fb"
abbrev ID := Fin 5
def col (i : ID) : BitVec 5 := ([3, 11, 9, 11, 4] : List (BitVec 5)).getD i.val 0
theorem checked : check col [0] [2, 3] 1 7 19 [0, 2, 3] [2] [4] = true := by decide
theorem result : ([0] : List ID).toFinset ⊆ support [0] [2, 3] ∧
    Exact (fun i => decode (col i)) (named 1 7 19) (support [0] [2, 3]) := sound col [0] [2, 3] 1 7 19 [0, 2, 3] [2] [4] checked
#print axioms result
end DirectInstance_feb6f1db2ffddcaab37df0439282c7f0458718dddc195ac9c87b29e90f8050fb

namespace DirectInstance_d701e8d81dbf263083e4530f126adf2fc6c49243e7dae5ecb429feb113d72cd5
open ThreeNamePacked ThreeNamePinReduction ThreeNameGenericPositive ThreeNameGenericDirect
def rawInputSHA256 : String := "d701e8d81dbf263083e4530f126adf2fc6c49243e7dae5ecb429feb113d72cd5"
abbrev ID := Fin 5
def col (i : ID) : BitVec 5 := ([3, 11, 9, 11, 4] : List (BitVec 5)).getD i.val 0
theorem checked : checkConflict col [0, 4] 1 7 19 true false false [0, 4] = true := by decide
theorem result (A : Finset ID) (h : ([0, 4] : List ID).toFinset ⊆ A) :
    ¬ Exact (fun i => decode (col i)) (named 1 7 19) A := conflict_no col [0, 4] 1 7 19 true false false [0, 4] checked A h
#print axioms result
end DirectInstance_d701e8d81dbf263083e4530f126adf2fc6c49243e7dae5ecb429feb113d72cd5

namespace DirectInstance_3e5814f0920d11bc76663870e6e34abb3e832ec0ec9410ecf6c9737b399fb644
open ThreeNamePacked ThreeNamePinReduction ThreeNameGenericPositive ThreeNameGenericDirect
def rawInputSHA256 : String := "3e5814f0920d11bc76663870e6e34abb3e832ec0ec9410ecf6c9737b399fb644"
abbrev ID := Fin 3
def col (i : ID) : BitVec 5 := ([2, 6, 20] : List (BitVec 5)).getD i.val 0
theorem checked : checkOutside col 1 [0] = true := by decide
theorem result (A : Finset ID) : ¬ Exact (fun i => decode (col i)) (named 1 2 4) A :=
  outside_no col 1 2 4 [0] checked A
#print axioms result
end DirectInstance_3e5814f0920d11bc76663870e6e34abb3e832ec0ec9410ecf6c9737b399fb644
