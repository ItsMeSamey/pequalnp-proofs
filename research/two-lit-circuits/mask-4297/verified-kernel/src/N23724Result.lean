import N23724Table
namespace Numeric23724
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def pf0 : List Nat := [261,1,261,1,1837,1,1795,1,1,1,1795,1,1,1,2051,1,1,1,259,1,1,1,259,1,1,1,283,1,1,1]
theorem row0 : checkRow table 0 pf0 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf1 : List Nat := [1029,1,261,1,261,1,261,1,283,1,1,1,1795,1,1,1,1795,1,1,1,0,1,1,1,2051,1,1,1,1027,1,1,1,1027,1,1,1,1051,1,1,1]
theorem row1 : checkRow table 1 pf1 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf2 : List Nat := [261,1,1029,1,261,1,261,1,1795,1,1,1,259,1,1,1,3115,1,1,1,259,1,1,1,3075,1,1,1,1027,1,1,1,259,1,1,1,2091,1,1,1,1835,1,1,1,1027,1,1,1]
theorem row2 : checkRow table 2 pf2 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf3 : List Nat := [261,1,517,1,261,1,261,1,261,1,1795,1,1,1,259,1,1,1,2563,1,1,1,515,1,1,1,259,1,1,1,4,1,1,1,3115,1,1,1,259,1,1,1,1835,1,1,1,515,1,1,1,3075,1,1,1,1027,1,1,1,259,1,1,1,2091,1,1,1,515,1,1,1,2099,1,1,1,1835,1,1,1,1027,1,1,1]
theorem row3 : checkRow table 3 pf3 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf4 : List Nat := [261,261,1029,1029,261,261,261,261,1819,2,3099,1,259,259,299,1,3075,1835,299,1,3075,4,3099,1,259,306183,259,1,283,1835,304927,1,3587,2091,3099,1,1027,1027,25472031,1,259,1027,259,1,2091,2091,306207,1,1027,1027,1835,1,1051,306207,306207,1]
theorem row4 : checkRow table 4 pf4 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf5 : List Nat := [261,261,517,517,261,261,261,261,261,261,1819,8963871,3099,1,259,259,299,1,2587,8694303,3099,1,515,515,587,1,259,515,259,1,8,306207,306207,1,3075,1835,299,1,3075,6,3099,1,259,2635,259,1,283,1835,304927,1,515,1835,515,1,539,2635,305695,1,3587,2091,3099,1,1027,1027,33860639,1,259,1027,259,1,2091,2091,306207,1,515,1027,515,1,2099,2891,306207,1,1027,1027,1835,1,1051,306207,306207,1]
theorem row5 : checkRow table 5 pf5 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
theorem allRows : Covered table table.size := by
  have hc : table.size = 6 := by simp [table]
  rw [hc]
  exact covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_zero table) row0) row1) row2) row3) row4) row5
theorem root0 : checkChild table (6,0,start) 261 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root1 : checkChild table (5,1,start) 10 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root2 : checkChild table (4,2,start) 306207 = true := by rw [childWith_eq table_at]; decide +kernel
end Numeric23724
