import N24202Page0
import N24202Page1
import N24202Page2
import N24202Page3
import N24202Table
namespace Numeric24202
set_option maxRecDepth 200000
set_option maxHeartbeats 0
theorem allRows : Covered table table.size := by
  have hc : table.size = 32 := by simp [table]
  rw [hc]
  exact covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_zero table) row0) row1) row2) row3) row4) row5) row6) row7) row8) row9) row10) row11) row12) row13) row14) row15) row16) row17) row18) row19) row20) row21) row22) row23) row24) row25) row26) row27) row28) row29) row30) row31
theorem root0 : checkChild table (6,0,[1986,30852,233736,860688,1721376]) 1285 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root1 : checkChild table (5,1,[1986,30852,233736,860688,1721376]) 62 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root2 : checkChild table (4,2,[1986,30852,233736,860688,1721376]) 58 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root3 : checkChild table (6,0,[63,1986,30852,233736,860688,1721376]) 1285 = true := by rw [childWith_eq table_at]; decide +kernel
theorem root4 : checkChild table (5,1,[63,1986,30852,233736,860688,1721376]) 60 = true := by rw [childWith_eq table_at]; decide +kernel
end Numeric24202
