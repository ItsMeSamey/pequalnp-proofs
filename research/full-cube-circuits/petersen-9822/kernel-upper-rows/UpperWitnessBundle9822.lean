import PEqualNP.Defs.MetaComplexity

-- Upper9822Base
namespace Research.Graph9822Steps
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4000

def step (w : List Bool) (g : Gate) := w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
def rows : List Gate := [
    ⟨.or, [2,6]⟩,
    ⟨.and, [1,10]⟩,
    ⟨.or, [3,0]⟩,
    ⟨.or, [12,9]⟩,
    ⟨.and, [4,13]⟩,
    ⟨.or, [0,7]⟩,
    ⟨.or, [15,8]⟩,
    ⟨.and, [5,16]⟩,
    ⟨.or, [2,9]⟩,
    ⟨.and, [7,18]⟩,
    ⟨.or, [3,6]⟩,
    ⟨.and, [8,20]⟩,
    ⟨.and, [9,6]⟩,
    ⟨.or, [11,14]⟩,
    ⟨.or, [23,17]⟩,
    ⟨.or, [24,19]⟩,
    ⟨.or, [25,21]⟩,
    ⟨.or, [26,22]⟩]
def witness : Circuit := ⟨rows, 27⟩

private def valid (g : Gate) : Bool :=
  (match g.op with
  | .and | .or | .not => true
  | _ => false) && decide (g.inputs.length ≤ 2)

private theorem valid_sound (g : Gate) (h : valid g = true) :
    g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  rcases g with ⟨op, ins⟩
  cases op <;> simp_all [valid]

theorem good : FanInTwo witness := by
  intro g hg
  have h : rows.all valid = true := by decide
  exact valid_sound g (List.all_eq_true.mp h g hg)

end Research.Graph9822Steps

-- Upper9822Part0
namespace Research.Graph9822Steps
open PEqualNP.CircuitLowerBounds
theorem s0 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9] ⟨.or, [2,6]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, (b2 || b6)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, (b2 || (b6 || false))] = _
  simp
theorem s1 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10] ⟨.and, [1,10]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, (b1 && b10)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, (b1 && (b10 && true))] = _
  simp
theorem s2 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11] ⟨.or, [3,0]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, (b3 || b0)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, (b3 || (b0 || false))] = _
  simp
theorem s3 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12] ⟨.or, [12,9]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, (b12 || b9)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, (b12 || (b9 || false))] = _
  simp
theorem s4 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13] ⟨.and, [4,13]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, (b4 && b13)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, (b4 && (b13 && true))] = _
  simp
theorem s5 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14] ⟨.or, [0,7]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, (b0 || b7)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, (b0 || (b7 || false))] = _
  simp
end Research.Graph9822Steps

-- Upper9822Part1
namespace Research.Graph9822Steps
open PEqualNP.CircuitLowerBounds
theorem s6 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15] ⟨.or, [15,8]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, (b15 || b8)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, (b15 || (b8 || false))] = _
  simp
theorem s7 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16] ⟨.and, [5,16]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, (b5 && b16)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, (b5 && (b16 && true))] = _
  simp
theorem s8 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17] ⟨.or, [2,9]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, (b2 || b9)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, (b2 || (b9 || false))] = _
  simp
theorem s9 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18] ⟨.and, [7,18]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, (b7 && b18)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, (b7 && (b18 && true))] = _
  simp
theorem s10 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19] ⟨.or, [3,6]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, (b3 || b6)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, (b3 || (b6 || false))] = _
  simp
theorem s11 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20] ⟨.and, [8,20]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, (b8 && b20)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, (b8 && (b20 && true))] = _
  simp
end Research.Graph9822Steps

-- Upper9822Part2
namespace Research.Graph9822Steps
open PEqualNP.CircuitLowerBounds
theorem s12 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21] ⟨.and, [9,6]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, (b9 && b6)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, (b9 && (b6 && true))] = _
  simp
theorem s13 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22] ⟨.or, [11,14]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, (b11 || b14)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, (b11 || (b14 || false))] = _
  simp
theorem s14 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23] ⟨.or, [23,17]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, (b23 || b17)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, (b23 || (b17 || false))] = _
  simp
theorem s15 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24] ⟨.or, [24,19]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, (b24 || b19)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, (b24 || (b19 || false))] = _
  simp
theorem s16 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25] ⟨.or, [25,21]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, (b25 || b21)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, (b25 || (b21 || false))] = _
  simp
theorem s17 (b0 b1 b2 b3 b4 b5 b6 b7 b8 b9 b10 b11 b12 b13 b14 b15 b16 b17 b18 b19 b20 b21 b22 b23 b24 b25 b26 : Bool) : step [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26] ⟨.or, [26,22]⟩ = [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, (b26 || b22)] := by
  change [b0, b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11, b12, b13, b14, b15, b16, b17, b18, b19, b20, b21, b22, b23, b24, b25, b26, (b26 || (b22 || false))] = _
  simp
end Research.Graph9822Steps

-- Upper9822Finish
namespace Research.Graph9822Steps
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
set_option maxRecDepth 4000
theorem upper : HasCircuitSize 10 (fun x => (x 1 && x 2) || (x 3 && x 4) || (x 0 && x 4) || (x 0 && x 5) || (x 1 && x 6) || (x 2 && x 7) || (x 3 && x 8) || (x 4 && x 9) || (x 5 && x 7) || (x 7 && x 9) || (x 6 && x 9) || (x 6 && x 8) || (x 5 && x 8)) 18 := by
  refine ⟨witness, good, by decide, ?_⟩
  intro x
  change (rows.foldl step [x 0, x 1, x 2, x 3, x 4, x 5, x 6, x 7, x 8, x 9]).getD 27 false = _
  simp only [rows, List.foldl_cons, List.foldl_nil, s0, s1, s2, s3, s4, s5, s6, s7, s8, s9, s10, s11, s12, s13, s14, s15, s16, s17]
  change (((((((x 1) && ((x 2) || (x 6))) || ((x 4) && (((x 3) || (x 0)) || (x 9)))) || ((x 5) && (((x 0) || (x 7)) || (x 8)))) || ((x 7) && ((x 2) || (x 9)))) || ((x 8) && ((x 3) || (x 6)))) || ((x 9) && (x 6))) = _
  simp only [Bool.and_or_distrib_left]
  ac_rfl
#print axioms upper
end Research.Graph9822Steps
