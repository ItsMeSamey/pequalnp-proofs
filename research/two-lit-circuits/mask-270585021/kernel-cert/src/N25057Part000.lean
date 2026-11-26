import N25057Table
import Numeric25057Closure
namespace Numeric25057
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def proof0 : List Nat := [3421,1,261,1,261,1,299,1,1,1,3331,1,1,1,3331,1,1,1]
theorem row0 : checkRow table 0 proof0 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof1 : List Nat := [3421,1,261,1,261,1,291,1,1,1,3331,1,1,1,3331,1,1,1]
theorem row1 : checkRow table 1 proof1 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof2 : List Nat := [261,1,3677,1,261,1,3331,1,1,1,259,1,1,1,3587,1,1,1,3587,1,1,1,299,1,1,1]
theorem row2 : checkRow table 2 proof2 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof3 : List Nat := [261,1,293,1,301,1,3331,1,1,1,3331,1,1,1,3587,1,1,1,3587,1,1,1,3419,1,1,1,291,1,1,1]
theorem row3 : checkRow table 3 proof3 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof4 : List Nat := [3677,1,261,1,261,1,299,1,1,1,3587,1,1,1,3587,1,1,1]
theorem row4 : checkRow table 4 proof4 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof5 : List Nat := [1797,1,261,1,261,1,261,1,4,1,1,1,3331,1,1,1,1795,1,1,1,299,1,1,1,3587,1,1,1,3587,1,1,1,1835,1,1,1]
theorem row5 : checkRow table 5 proof5 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof6 : List Nat := [261,1,3421,1,309,1,261,1,3371,1,1,1,314671,1,1,1,3371,1,1,1,0,1,1,1,3331,1,1,1,3331,1,1,1,1875,1,1,1,3379,1,1,1,3379,1,1,1]
theorem row6 : checkRow table 6 proof6 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof7 : List Nat := [261,1,3421,1,309,1,261,1,3363,1,1,1,314663,1,1,1,3363,1,1,1,2,1,1,1,3331,1,1,1,3331,1,1,1,1875,1,1,1,3379,1,1,1,3379,1,1,1]
theorem row7 : checkRow table 7 proof7 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof8 : List Nat := [261,1,309,1,3677,1,261,1,3627,1,1,1,4,1,1,1,3331,1,1,1,3331,1,1,1,3379,1,1,1,1843,1,1,1,3587,1,1,1,3587,1,1,1,3635,1,1,1,3635,1,1,1,1875,1,1,1]
theorem row8 : checkRow table 8 proof8 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof9 : List Nat := [261,1,309,1,293,1,301,1,3363,1,1,1,6,1,1,1,3331,1,1,1,3331,1,1,1,3635,1,1,1,1843,1,1,1,3587,1,1,1,3587,1,1,1,3419,1,1,1,1843,1,1,1]
theorem row9 : checkRow table 9 proof9 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof10 : List Nat := [261,1,3677,1,309,1,261,1,3627,1,1,1,314927,1,1,1,3627,1,1,1,8,1,1,1,3587,1,1,1,3587,1,1,1,1875,1,1,1,3635,1,1,1,3635,1,1,1]
theorem row10 : checkRow table 10 proof10 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof11 : List Nat := [3421,1,261,1,261,1,261,1,4,1,1,1,3331,1,1,1,299,1,1,1,3587,1,1,1,3587,1,1,1,0,1,1,1]
theorem row11 : checkRow table 11 proof11 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof12 : List Nat := [3421,1,261,1,261,1,261,1,291,1,1,1,3331,1,1,1,3331,1,1,1,299,1,1,1,3587,1,1,1,3587,1,1,1,2,1,1,1]
theorem row12 : checkRow table 12 proof12 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof13 : List Nat := [261,261,309,309,261,261,3371,3411,3371,1,259,259,307,1,3331,3419,307,1,3331,347399,3371,1,259,3419,259,1,299,314671,3411,1]
theorem row13 : checkRow table 13 proof13 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof14 : List Nat := [261,1,261,1,261,1,3333,1,3363,1,1,1,1843,1,1,1,3347,1,1,1,4915,1,1,1,1843,1,1,1,3347,1,1,1,259,1,1,1,275,1,1,1,259,1,1,1,291,1,1,1]
theorem row14 : checkRow table 14 proof14 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof15 : List Nat := [309,1,261,1,293,1,261,1,3419,1,1,1,291,1,1,1,3331,1,1,1,3331,1,1,1,291,1,1,1,6,1,1,1,3587,1,1,1,3587,1,1,1,339,1,1,1]
theorem row15 : checkRow table 15 proof15 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
theorem advance16 (prior : Covered table 0) : Covered table 16 :=
covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (prior) row0) row1) row2) row3) row4) row5) row6) row7) row8) row9) row10) row11) row12) row13) row14) row15
end Numeric25057
