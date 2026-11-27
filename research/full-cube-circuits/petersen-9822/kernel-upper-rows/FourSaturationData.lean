import Std
namespace Research.Graph9822.FourSaturation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def edges : List (Nat × Nat) :=
  [(1,2),(3,4),(0,4),(0,5),(1,6),(2,7),(3,8),(4,9),(5,7),(7,9),(6,9),(6,8),(5,8)]
def accepts (m : Nat) : Bool := edges.any fun e => m.testBit e.1 && m.testBit e.2
def maximalNegative (m : Nat) : Bool :=
  !accepts m && (List.range 10).all fun i => m.testBit i || accepts (m ||| (1 <<< i))
def witnesses : List Nat :=
  [50,77,108,116,139,201,208,276,387,402,523,525,554,556,771,773]

theorem sixteen_distinct : witnesses.length = 16 ∧ witnesses.Nodup := by decide
theorem all_maximal : witnesses.all maximalNegative = true := by decide
theorem vertex_one_count : (witnesses.filter fun m => m.testBit 1).length = 7 := by decide

/-- Bit 2*i+b selects the ray on which direction bit i equals b. -/
def rayUnionContains (rays word : Nat) : Bool :=
  (List.range 4).any fun i => rays.testBit (2*i + (if word.testBit i then 1 else 0))
def omissionCount (rays : Nat) : Nat :=
  ((List.range 16).filter fun word => !rayUnionContains rays word).length

theorem omission_count_ne_seven (r : Fin 256) : omissionCount r.val ≠ 7 := by
  have h : ∀ i : Fin 256, omissionCount i.val ≠ 7 := by decide
  exact h r

end Research.Graph9822.FourSaturation
