import N24202Table
namespace Numeric24202
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def pf0 : List Nat := [1285,1,2309,1,2053,1,1315,1,1,1,2059,1,1,1,1307,1,1,1,2315,1,1,1,2059,1,1,1,1307,1,1,1]
theorem row0 : checkRow table 0 pf0 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf1 : List Nat := [1285,1,4101,1,2053,1,1315,1,1,1,2059,1,1,1,1291,1,1,1,4123,1,1,1,2075,1,1,1,1291,1,1,1]
theorem row1 : checkRow table 1 pf1 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf2 : List Nat := [1285,1,4101,1,2309,1,1307,1,1,1,2315,1,1,1,1291,1,1,1,4123,1,1,1,2339,1,1,1,1291,1,1,1]
theorem row2 : checkRow table 2 pf2 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf3 : List Nat := [1285,1,1285,1,2309,1,2053,1,2075,1,1,1,0,1,1,1,3091,1,1,1,2059,1,1,1,2059,1,1,1,3091,1,1,1,3347,1,1,1,2315,1,1,1,2315,1,1,1,3347,1,1,1,2059,1,1,1,1307,1,1,1]
theorem row3 : checkRow table 3 pf3 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf4 : List Nat := [1285,1,1285,1,2053,1,2053,1,3091,1,1,1,2059,1,1,1,2075,1,1,1,2,1,1,1,2059,1,1,1,3091,1,1,1,1299,1,1,1,2315,1,1,1,2059,1,1,1,4123,1,1,1,2315,1,1,1,1299,1,1,1]
theorem row4 : checkRow table 4 pf4 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf5 : List Nat := [1285,1,1285,1,2053,1,2309,1,3347,1,1,1,2315,1,1,1,1307,1,1,1,4,1,1,1,2315,1,1,1,3347,1,1,1,1299,1,1,1,2059,1,1,1,2059,1,1,1,4123,1,1,1,2059,1,1,1,1299,1,1,1]
theorem row5 : checkRow table 5 pf5 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf6 : List Nat := [1285,1,1285,1,3077,1,2053,1,2059,1,1,1,3091,1,1,1,2075,1,1,1,2,1,1,1,3091,1,1,1,2059,1,1,1,1291,1,1,1,3347,1,1,1,1291,1,1,1,4123,1,1,1,3347,1,1,1,1291,1,1,1]
theorem row6 : checkRow table 6 pf6 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf7 : List Nat := [1285,1,1285,1,3077,1,2309,1,2315,1,1,1,3347,1,1,1,1307,1,1,1,4,1,1,1,3347,1,1,1,2315,1,1,1,1291,1,1,1,3091,1,1,1,1291,1,1,1,4123,1,1,1,3091,1,1,1,1291,1,1,1]
theorem row7 : checkRow table 7 pf7 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
end Numeric24202
