import N25057Table
import Numeric25057Closure
namespace Numeric25057
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def proof32 : List Nat := [261,1,3421,1,309,1,261,1,261,1,3627,1,1,1,314927,1,1,1,3627,1,1,1,22,1,1,1,3331,1,1,1,16,1,1,1,3379,1,1,1,3587,1,1,1,3587,1,1,1,1875,1,1,1,3635,1,1,1,3635,1,1,1,12,1,1,1]
theorem row32 : checkRow table 32 proof32 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof33 : List Nat := [261,1,3421,1,309,1,261,1,261,1,3363,1,1,1,314663,1,1,1,3363,1,1,1,24,1,1,1,3331,1,1,1,3331,1,1,1,8687191,1,1,1,3379,1,1,1,3587,1,1,1,3587,1,1,1,1875,1,1,1,3635,1,1,1,3635,1,1,1,14,1,1,1]
theorem row33 : checkRow table 33 proof33 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof34 : List Nat := [261,1,309,1,261,1,261,1,261,1,10,1,1,1,32,1,1,1,259,1,1,1,1843,1,1,1,3419,1,1,1,1843,1,1,1,307,1,1,1,339,1,1,1,259,1,1,1,299,1,1,1,3675,1,1,1,314887,1,1,1,1875,1,1,1]
theorem row34 : checkRow table 34 proof34 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof35 : List Nat := [261,1,309,1,261,1,261,1,261,1,1811,1,1,1,307,1,1,1,32,1,1,1,259,1,1,1,275,1,1,1,3419,1,1,1,1843,1,1,1,307,1,1,1,339,1,1,1,259,1,1,1,299,1,1,1,3675,1,1,1,314887,1,1,1,1875,1,1,1]
theorem row35 : checkRow table 35 proof35 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof36 : List Nat := [261,1,309,1,261,1,261,1,261,1,1811,1,1,1,307,1,1,1,34,1,1,1,259,1,1,1,275,1,1,1,314671,1,1,1,1843,1,1,1,307,1,1,1,339,1,1,1,259,1,1,1,299,1,1,1,3419,1,1,1,316167,1,1,1,1843,1,1,1,1875,1,1,1]
theorem row36 : checkRow table 36 proof36 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof37 : List Nat := [261,261,309,309,261,261,261,261,1811,3411,3371,1,259,259,307,1,3371,1875,3371,1,307,8654167,307,1,3411,3419,3411,1,259,1875,259,1,3363,1843,307,1,3363,8654167,3371,1,259,3475,259,1,275,1843,3411,1,3475,3475,314671,1,1843,1843,1875,1]
theorem row37 : checkRow table 37 proof37 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof38 : List Nat := [261,261,309,309,261,261,261,261,3627,3667,3627,1,259,259,307,1,3331,8654423,265815,1,259,3419,259,1,1843,1843,314927,1,3627,3675,3627,1,307,8654423,307,1,3667,3675,3667,1,259,314927,259,1]
theorem row38 : checkRow table 38 proof38 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof39 : List Nat := [261,261,309,309,261,261,261,261,3627,3667,3627,1,259,259,307,1,3331,8654423,265815,1,259,3419,259,1,1843,1843,314927,1,3587,3675,307,1,3587,347655,3627,1,259,3675,259,1,299,314927,3667,1,1875,314927,314927,1]
theorem row39 : checkRow table 39 proof39 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof40 : List Nat := [261,261,309,309,261,261,261,261,3587,3667,3587,1,259,259,339,1,38,8654423,265815,1,259,3419,259,1,1843,1843,347655,1,3635,3675,347655,1,259,314887,259,1,1875,347655,347655,1]
theorem row40 : checkRow table 40 proof40 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof41 : List Nat := [261,261,309,309,261,261,301,301,3627,3635,3627,1,299,299,307,1,3331,8695351,306743,1,299,3419,299,1,1843,1843,314927,1,3587,3675,314927,1,3587,314887,3627,1,3419,3675,3419,1,1843,314927,1843,1]
theorem row41 : checkRow table 41 proof41 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof42 : List Nat := [261,261,309,309,261,261,261,261,3627,3667,3627,1,259,259,307,1,3371,8654423,265815,1,259,314671,259,1,1875,1875,314927,1,3587,3675,307,1,3587,347655,3627,1,259,3675,259,1,299,314927,3667,1]
theorem row42 : checkRow table 42 proof42 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof43 : List Nat := [261,261,309,309,261,261,261,261,1811,3667,3347,1,259,259,307,1,3331,1843,3627,1,3331,8654423,3347,1,259,3419,259,1,275,1843,313111,1,3587,3675,3347,1,3587,347655,3627,1,259,3675,259,1,299,314647,3667,1,1875,314647,314647,1]
theorem row43 : checkRow table 43 proof43 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof44 : List Nat := [261,1,309,1,3677,1,261,1,261,1,3363,1,1,1,40,1,1,1,3627,1,1,1,3363,1,1,1,3403,1,1,1,1843,1,1,1,3627,1,1,1,3363,1,1,1,291,1,1,1,291,1,1,1,1843,1,1,1,1867,1,1,1,3587,1,1,1,3587,1,1,1,3635,1,1,1,3635,1,1,1,1875,1,1,1,3675,1,1,1,3731,1,1,1]
theorem row44 : checkRow table 44 proof44 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof45 : List Nat := [261,261,309,309,293,293,261,261,1827,3667,3363,1,291,291,30,1,3331,1843,3627,1,3331,8654423,3363,1,3379,3419,3667,1,291,1843,291,1,3587,3675,3363,1,3587,8687191,3627,1,291,3675,291,1,3635,18,3667,1,1875,8687191,8687191,1]
theorem row45 : checkRow table 45 proof45 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof46 : List Nat := [261,261,309,309,261,261,261,261,1795,3667,3331,1,259,259,32,1,3379,3419,3667,1,259,1843,259,1,3331,3675,3331,1,38,8654423,265815,1,259,3675,259,1,299,8695351,3667,1,1843,3675,1843,1,1875,8654423,8654423,1]
theorem row46 : checkRow table 46 proof46 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
def proof47 : List Nat := [261,1,309,1,309,1,261,1,261,1,3627,1,1,1,42,1,1,1,3331,1,1,1,3331,1,1,1,3379,1,1,1,1843,1,1,1,16,1,1,1,1843,1,1,1,3587,1,1,1,3587,1,1,1,3675,1,1,1,8696631,1,1,1,3419,1,1,1,8696631,1,1,1,1843,1,1,1,1875,1,1,1]
theorem row47 : checkRow table 47 proof47 = true := by rw [rowWith_eq table_at, rowWith_eval]; decide +kernel
theorem advance48 (prior : Covered table 32) : Covered table 48 :=
covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (covered_succ (prior) row32) row33) row34) row35) row36) row37) row38) row39) row40) row41) row42) row43) row44) row45) row46) row47
end Numeric25057
