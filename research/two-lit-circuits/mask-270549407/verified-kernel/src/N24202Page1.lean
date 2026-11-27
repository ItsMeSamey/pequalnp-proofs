import N24202Table
namespace Numeric24202
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def pf8 : List Nat := [4101,1,2309,1,1285,1,2053,1,2339,1,1,1,2059,1,1,1,1283,1,1,1,2563,1,1,1,1283,1,1,1,4355,1,1,1,2075,1,1,1,2315,1,1,1,2059,1,1,1,4123,1,1,1,1283,1,1,1,4867,1,1,1]
theorem row8 : checkRow table 8 pf8 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf9 : List Nat := [1285,1,1285,1,1285,1,2053,1,2339,1,1,1,2059,1,1,1,2307,1,1,1,2307,1,1,1,4099,1,1,1,4099,1,1,1,1283,1,1,1,1291,1,1,1,1283,1,1,1,1307,1,1,1,4867,1,1,1,1283,1,1,1]
theorem row9 : checkRow table 9 pf9 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf10 : List Nat := [1285,1,1285,1,2053,1,2053,1,2339,1,1,1,2059,1,1,1,2075,1,1,1,2,1,1,1,2059,1,1,1,0,1,1,1,2075,1,1,1,2315,1,1,1,2059,1,1,1,4123,1,1,1]
theorem row10 : checkRow table 10 pf10 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf11 : List Nat := [1285,1,1285,1,2053,1,2309,1,2075,1,1,1,2315,1,1,1,1307,1,1,1,4,1,1,1,2315,1,1,1,0,1,1,1,2339,1,1,1,2059,1,1,1,2059,1,1,1,4123,1,1,1]
theorem row11 : checkRow table 11 pf11 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf12 : List Nat := [1285,1,1285,1,2309,1,1285,1,2075,1,1,1,2315,1,1,1,1283,1,1,1,1291,1,1,1,1283,1,1,1,1315,1,1,1,2051,1,1,1,2051,1,1,1,4099,1,1,1,4099,1,1,1,4355,1,1,1,1283,1,1,1]
theorem row12 : checkRow table 12 pf12 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf13 : List Nat := [1285,1,1285,1,2053,1,4101,1,2059,1,1,1,4123,1,1,1,1291,1,1,1,4,1,1,1,1291,1,1,1,2,1,1,1,2339,1,1,1,2059,1,1,1,2075,1,1,1,2315,1,1,1]
theorem row13 : checkRow table 13 pf13 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf14 : List Nat := [1285,1,1285,1,4101,1,1285,1,2059,1,1,1,4123,1,1,1,1283,1,1,1,1307,1,1,1,1283,1,1,1,1315,1,1,1,2051,1,1,1,2051,1,1,1,2307,1,1,1,2307,1,1,1,2563,1,1,1,1283,1,1,1]
theorem row14 : checkRow table 14 pf14 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def pf15 : List Nat := [28,1,24,1,18,1,16,1,2339,1,1,1,2059,1,1,1,2075,1,1,1,2315,1,1,1,2059,1,1,1,4123,1,1,1,1283,1,1,1,1291,1,1,1,1283,1,1,1,1307,1,1,1,1283,1,1,1,1315,1,1,1]
theorem row15 : checkRow table 15 pf15 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
end Numeric24202
