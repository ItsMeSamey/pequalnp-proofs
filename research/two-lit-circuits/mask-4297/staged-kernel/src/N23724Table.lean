import TableFastSupport23724
import Numeric23724Closure
namespace Numeric23724
set_option maxRecDepth 200000
set_option maxHeartbeats 0
def fastKey : Nat → Key
  | 0 => (2,1,[31,13448,26902])
  | 1 => (3,1,[6,31,13448,26896])
  | 2 => (3,1,[31,4070,13471,26896])
  | 3 => (4,1,[31,482,3652,13471,26896])
  | 4 => (4,1,[31,4070,13448,26896])
  | 5 => (5,1,[31,482,3652,13448,26896])
  | _ => (0,0,[])
def table : Array Key := Array.ofFn (fun i : Fin 6 => fastKey i.val)
def atKey (i : Nat) : Option Key := if i < 6 then some (fastKey i) else none
theorem table_at (i : Nat) : table[i]? = atKey i := by
  by_cases hi : i < 6 <;> simp [table, atKey, hi, getElem?_def]
end Numeric23724
