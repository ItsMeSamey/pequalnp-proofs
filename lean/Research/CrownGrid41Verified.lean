import PEqualNP.Defs.Represents

namespace CrownGrid
open PEqualNP.CircuitLowerBounds PEqualNP.Represents PEqualNP.MetaComplexity
def circuit : Circuit := ⟨[
    ⟨.or, [0,12]⟩,
    ⟨.or, [1,13]⟩,
    ⟨.or, [2,14]⟩,
    ⟨.or, [3,15]⟩,
    ⟨.or, [4,16]⟩,
    ⟨.or, [5,17]⟩,
    ⟨.or, [6,18]⟩,
    ⟨.or, [7,19]⟩,
    ⟨.or, [8,20]⟩,
    ⟨.or, [9,21]⟩,
    ⟨.or, [10,22]⟩,
    ⟨.or, [11,23]⟩,
    ⟨.or, [24,25]⟩,
    ⟨.or, [36,26]⟩,
    ⟨.or, [37,27]⟩,
    ⟨.or, [28,29]⟩,
    ⟨.or, [39,30]⟩,
    ⟨.or, [40,31]⟩,
    ⟨.or, [32,33]⟩,
    ⟨.or, [42,34]⟩,
    ⟨.or, [43,35]⟩,
    ⟨.or, [24,28]⟩,
    ⟨.or, [45,32]⟩,
    ⟨.or, [25,29]⟩,
    ⟨.or, [47,33]⟩,
    ⟨.or, [26,30]⟩,
    ⟨.or, [49,34]⟩,
    ⟨.or, [27,31]⟩,
    ⟨.or, [51,35]⟩,
    ⟨.and, [38,41]⟩,
    ⟨.or, [38,41]⟩,
    ⟨.and, [54,44]⟩,
    ⟨.or, [53,55]⟩,
    ⟨.and, [46,48]⟩,
    ⟨.and, [50,52]⟩,
    ⟨.or, [57,58]⟩,
    ⟨.or, [46,48]⟩,
    ⟨.or, [50,52]⟩,
    ⟨.and, [60,61]⟩,
    ⟨.or, [59,62]⟩,
    ⟨.or, [56,63]⟩], 64⟩

private def formula (i j : Fin 12) : Bool :=
  let w0 := decide ((0 : Fin 12) = i)
  let w1 := decide ((1 : Fin 12) = i)
  let w2 := decide ((2 : Fin 12) = i)
  let w3 := decide ((3 : Fin 12) = i)
  let w4 := decide ((4 : Fin 12) = i)
  let w5 := decide ((5 : Fin 12) = i)
  let w6 := decide ((6 : Fin 12) = i)
  let w7 := decide ((7 : Fin 12) = i)
  let w8 := decide ((8 : Fin 12) = i)
  let w9 := decide ((9 : Fin 12) = i)
  let w10 := decide ((10 : Fin 12) = i)
  let w11 := decide ((11 : Fin 12) = i)
  let w12 := decide ((0 : Fin 12) = j)
  let w13 := decide ((1 : Fin 12) = j)
  let w14 := decide ((2 : Fin 12) = j)
  let w15 := decide ((3 : Fin 12) = j)
  let w16 := decide ((4 : Fin 12) = j)
  let w17 := decide ((5 : Fin 12) = j)
  let w18 := decide ((6 : Fin 12) = j)
  let w19 := decide ((7 : Fin 12) = j)
  let w20 := decide ((8 : Fin 12) = j)
  let w21 := decide ((9 : Fin 12) = j)
  let w22 := decide ((10 : Fin 12) = j)
  let w23 := decide ((11 : Fin 12) = j)
  let w24 := GateOp.eval .or [w0, w12]
  let w25 := GateOp.eval .or [w1, w13]
  let w26 := GateOp.eval .or [w2, w14]
  let w27 := GateOp.eval .or [w3, w15]
  let w28 := GateOp.eval .or [w4, w16]
  let w29 := GateOp.eval .or [w5, w17]
  let w30 := GateOp.eval .or [w6, w18]
  let w31 := GateOp.eval .or [w7, w19]
  let w32 := GateOp.eval .or [w8, w20]
  let w33 := GateOp.eval .or [w9, w21]
  let w34 := GateOp.eval .or [w10, w22]
  let w35 := GateOp.eval .or [w11, w23]
  let w36 := GateOp.eval .or [w24, w25]
  let w37 := GateOp.eval .or [w36, w26]
  let w38 := GateOp.eval .or [w37, w27]
  let w39 := GateOp.eval .or [w28, w29]
  let w40 := GateOp.eval .or [w39, w30]
  let w41 := GateOp.eval .or [w40, w31]
  let w42 := GateOp.eval .or [w32, w33]
  let w43 := GateOp.eval .or [w42, w34]
  let w44 := GateOp.eval .or [w43, w35]
  let w45 := GateOp.eval .or [w24, w28]
  let w46 := GateOp.eval .or [w45, w32]
  let w47 := GateOp.eval .or [w25, w29]
  let w48 := GateOp.eval .or [w47, w33]
  let w49 := GateOp.eval .or [w26, w30]
  let w50 := GateOp.eval .or [w49, w34]
  let w51 := GateOp.eval .or [w27, w31]
  let w52 := GateOp.eval .or [w51, w35]
  let w53 := GateOp.eval .and [w38, w41]
  let w54 := GateOp.eval .or [w38, w41]
  let w55 := GateOp.eval .and [w54, w44]
  let w56 := GateOp.eval .or [w53, w55]
  let w57 := GateOp.eval .and [w46, w48]
  let w58 := GateOp.eval .and [w50, w52]
  let w59 := GateOp.eval .or [w57, w58]
  let w60 := GateOp.eval .or [w46, w48]
  let w61 := GateOp.eval .or [w50, w52]
  let w62 := GateOp.eval .and [w60, w61]
  let w63 := GateOp.eval .or [w59, w62]
  let w64 := GateOp.eval .or [w56, w63]
  w64

set_option maxRecDepth 100000
set_option maxHeartbeats 0
private def finish (gs : List Gate) (vs : List Bool) : Bool :=
  (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) vs).getD 64 false

private theorem finish_cons (g : Gate) (gs : List Gate) (vs next : List Bool)
    (h : vs ++ [g.op.eval (g.inputs.map fun i => vs.getD i false)] = next) :
    finish (g :: gs) vs = finish gs next := by subst next; rfl

private theorem eval_formula (i j : Fin 12) : circuit.eval (oneEach i j) = formula i j := by
  let w0 := decide ((0 : Fin 12) = i)
  let w1 := decide ((1 : Fin 12) = i)
  let w2 := decide ((2 : Fin 12) = i)
  let w3 := decide ((3 : Fin 12) = i)
  let w4 := decide ((4 : Fin 12) = i)
  let w5 := decide ((5 : Fin 12) = i)
  let w6 := decide ((6 : Fin 12) = i)
  let w7 := decide ((7 : Fin 12) = i)
  let w8 := decide ((8 : Fin 12) = i)
  let w9 := decide ((9 : Fin 12) = i)
  let w10 := decide ((10 : Fin 12) = i)
  let w11 := decide ((11 : Fin 12) = i)
  let w12 := decide ((0 : Fin 12) = j)
  let w13 := decide ((1 : Fin 12) = j)
  let w14 := decide ((2 : Fin 12) = j)
  let w15 := decide ((3 : Fin 12) = j)
  let w16 := decide ((4 : Fin 12) = j)
  let w17 := decide ((5 : Fin 12) = j)
  let w18 := decide ((6 : Fin 12) = j)
  let w19 := decide ((7 : Fin 12) = j)
  let w20 := decide ((8 : Fin 12) = j)
  let w21 := decide ((9 : Fin 12) = j)
  let w22 := decide ((10 : Fin 12) = j)
  let w23 := decide ((11 : Fin 12) = j)
  let w24 := GateOp.eval .or [w0, w12]
  let w25 := GateOp.eval .or [w1, w13]
  let w26 := GateOp.eval .or [w2, w14]
  let w27 := GateOp.eval .or [w3, w15]
  let w28 := GateOp.eval .or [w4, w16]
  let w29 := GateOp.eval .or [w5, w17]
  let w30 := GateOp.eval .or [w6, w18]
  let w31 := GateOp.eval .or [w7, w19]
  let w32 := GateOp.eval .or [w8, w20]
  let w33 := GateOp.eval .or [w9, w21]
  let w34 := GateOp.eval .or [w10, w22]
  let w35 := GateOp.eval .or [w11, w23]
  let w36 := GateOp.eval .or [w24, w25]
  let w37 := GateOp.eval .or [w36, w26]
  let w38 := GateOp.eval .or [w37, w27]
  let w39 := GateOp.eval .or [w28, w29]
  let w40 := GateOp.eval .or [w39, w30]
  let w41 := GateOp.eval .or [w40, w31]
  let w42 := GateOp.eval .or [w32, w33]
  let w43 := GateOp.eval .or [w42, w34]
  let w44 := GateOp.eval .or [w43, w35]
  let w45 := GateOp.eval .or [w24, w28]
  let w46 := GateOp.eval .or [w45, w32]
  let w47 := GateOp.eval .or [w25, w29]
  let w48 := GateOp.eval .or [w47, w33]
  let w49 := GateOp.eval .or [w26, w30]
  let w50 := GateOp.eval .or [w49, w34]
  let w51 := GateOp.eval .or [w27, w31]
  let w52 := GateOp.eval .or [w51, w35]
  let w53 := GateOp.eval .and [w38, w41]
  let w54 := GateOp.eval .or [w38, w41]
  let w55 := GateOp.eval .and [w54, w44]
  let w56 := GateOp.eval .or [w53, w55]
  let w57 := GateOp.eval .and [w46, w48]
  let w58 := GateOp.eval .and [w50, w52]
  let w59 := GateOp.eval .or [w57, w58]
  let w60 := GateOp.eval .or [w46, w48]
  let w61 := GateOp.eval .or [w50, w52]
  let w62 := GateOp.eval .and [w60, w61]
  let w63 := GateOp.eval .or [w59, w62]
  let w64 := GateOp.eval .or [w56, w63]
  calc
    circuit.eval (oneEach i j) = finish circuit.gates [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23] := congrArg (finish circuit.gates) (by rfl)
    _ = finish (circuit.gates.drop 1) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24] := finish_cons ⟨.or, [0, 12]⟩ (circuit.gates.drop 1) _ _ (by rfl)
    _ = finish (circuit.gates.drop 2) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25] := finish_cons ⟨.or, [1, 13]⟩ (circuit.gates.drop 2) _ _ (by rfl)
    _ = finish (circuit.gates.drop 3) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26] := finish_cons ⟨.or, [2, 14]⟩ (circuit.gates.drop 3) _ _ (by rfl)
    _ = finish (circuit.gates.drop 4) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27] := finish_cons ⟨.or, [3, 15]⟩ (circuit.gates.drop 4) _ _ (by rfl)
    _ = finish (circuit.gates.drop 5) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28] := finish_cons ⟨.or, [4, 16]⟩ (circuit.gates.drop 5) _ _ (by rfl)
    _ = finish (circuit.gates.drop 6) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29] := finish_cons ⟨.or, [5, 17]⟩ (circuit.gates.drop 6) _ _ (by rfl)
    _ = finish (circuit.gates.drop 7) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30] := finish_cons ⟨.or, [6, 18]⟩ (circuit.gates.drop 7) _ _ (by rfl)
    _ = finish (circuit.gates.drop 8) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31] := finish_cons ⟨.or, [7, 19]⟩ (circuit.gates.drop 8) _ _ (by rfl)
    _ = finish (circuit.gates.drop 9) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32] := finish_cons ⟨.or, [8, 20]⟩ (circuit.gates.drop 9) _ _ (by rfl)
    _ = finish (circuit.gates.drop 10) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33] := finish_cons ⟨.or, [9, 21]⟩ (circuit.gates.drop 10) _ _ (by rfl)
    _ = finish (circuit.gates.drop 11) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34] := finish_cons ⟨.or, [10, 22]⟩ (circuit.gates.drop 11) _ _ (by rfl)
    _ = finish (circuit.gates.drop 12) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35] := finish_cons ⟨.or, [11, 23]⟩ (circuit.gates.drop 12) _ _ (by rfl)
    _ = finish (circuit.gates.drop 13) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36] := finish_cons ⟨.or, [24, 25]⟩ (circuit.gates.drop 13) _ _ (by rfl)
    _ = finish (circuit.gates.drop 14) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37] := finish_cons ⟨.or, [36, 26]⟩ (circuit.gates.drop 14) _ _ (by rfl)
    _ = finish (circuit.gates.drop 15) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38] := finish_cons ⟨.or, [37, 27]⟩ (circuit.gates.drop 15) _ _ (by rfl)
    _ = finish (circuit.gates.drop 16) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39] := finish_cons ⟨.or, [28, 29]⟩ (circuit.gates.drop 16) _ _ (by rfl)
    _ = finish (circuit.gates.drop 17) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40] := finish_cons ⟨.or, [39, 30]⟩ (circuit.gates.drop 17) _ _ (by rfl)
    _ = finish (circuit.gates.drop 18) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41] := finish_cons ⟨.or, [40, 31]⟩ (circuit.gates.drop 18) _ _ (by rfl)
    _ = finish (circuit.gates.drop 19) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42] := finish_cons ⟨.or, [32, 33]⟩ (circuit.gates.drop 19) _ _ (by rfl)
    _ = finish (circuit.gates.drop 20) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43] := finish_cons ⟨.or, [42, 34]⟩ (circuit.gates.drop 20) _ _ (by rfl)
    _ = finish (circuit.gates.drop 21) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44] := finish_cons ⟨.or, [43, 35]⟩ (circuit.gates.drop 21) _ _ (by rfl)
    _ = finish (circuit.gates.drop 22) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45] := finish_cons ⟨.or, [24, 28]⟩ (circuit.gates.drop 22) _ _ (by rfl)
    _ = finish (circuit.gates.drop 23) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46] := finish_cons ⟨.or, [45, 32]⟩ (circuit.gates.drop 23) _ _ (by rfl)
    _ = finish (circuit.gates.drop 24) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47] := finish_cons ⟨.or, [25, 29]⟩ (circuit.gates.drop 24) _ _ (by rfl)
    _ = finish (circuit.gates.drop 25) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48] := finish_cons ⟨.or, [47, 33]⟩ (circuit.gates.drop 25) _ _ (by rfl)
    _ = finish (circuit.gates.drop 26) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49] := finish_cons ⟨.or, [26, 30]⟩ (circuit.gates.drop 26) _ _ (by rfl)
    _ = finish (circuit.gates.drop 27) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50] := finish_cons ⟨.or, [49, 34]⟩ (circuit.gates.drop 27) _ _ (by rfl)
    _ = finish (circuit.gates.drop 28) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51] := finish_cons ⟨.or, [27, 31]⟩ (circuit.gates.drop 28) _ _ (by rfl)
    _ = finish (circuit.gates.drop 29) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52] := finish_cons ⟨.or, [51, 35]⟩ (circuit.gates.drop 29) _ _ (by rfl)
    _ = finish (circuit.gates.drop 30) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53] := finish_cons ⟨.and, [38, 41]⟩ (circuit.gates.drop 30) _ _ (by rfl)
    _ = finish (circuit.gates.drop 31) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54] := finish_cons ⟨.or, [38, 41]⟩ (circuit.gates.drop 31) _ _ (by rfl)
    _ = finish (circuit.gates.drop 32) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55] := finish_cons ⟨.and, [54, 44]⟩ (circuit.gates.drop 32) _ _ (by rfl)
    _ = finish (circuit.gates.drop 33) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56] := finish_cons ⟨.or, [53, 55]⟩ (circuit.gates.drop 33) _ _ (by rfl)
    _ = finish (circuit.gates.drop 34) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57] := finish_cons ⟨.and, [46, 48]⟩ (circuit.gates.drop 34) _ _ (by rfl)
    _ = finish (circuit.gates.drop 35) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58] := finish_cons ⟨.and, [50, 52]⟩ (circuit.gates.drop 35) _ _ (by rfl)
    _ = finish (circuit.gates.drop 36) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59] := finish_cons ⟨.or, [57, 58]⟩ (circuit.gates.drop 36) _ _ (by rfl)
    _ = finish (circuit.gates.drop 37) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60] := finish_cons ⟨.or, [46, 48]⟩ (circuit.gates.drop 37) _ _ (by rfl)
    _ = finish (circuit.gates.drop 38) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61] := finish_cons ⟨.or, [50, 52]⟩ (circuit.gates.drop 38) _ _ (by rfl)
    _ = finish (circuit.gates.drop 39) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62] := finish_cons ⟨.and, [60, 61]⟩ (circuit.gates.drop 39) _ _ (by rfl)
    _ = finish (circuit.gates.drop 40) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63] := finish_cons ⟨.or, [59, 62]⟩ (circuit.gates.drop 40) _ _ (by rfl)
    _ = finish (circuit.gates.drop 41) [w0, w1, w2, w3, w4, w5, w6, w7, w8, w9, w10, w11, w12, w13, w14, w15, w16, w17, w18, w19, w20, w21, w22, w23, w24, w25, w26, w27, w28, w29, w30, w31, w32, w33, w34, w35, w36, w37, w38, w39, w40, w41, w42, w43, w44, w45, w46, w47, w48, w49, w50, w51, w52, w53, w54, w55, w56, w57, w58, w59, w60, w61, w62, w63, w64] := finish_cons ⟨.or, [56, 63]⟩ (circuit.gates.drop 41) _ _ (by rfl)
    _ = formula i j := rfl

theorem grid_upper : Monotone2 circuit ∧ circuit.size = 41 ∧
    (circuit.gates.filter (fun g => match g.op with | .and => true | _ => false)).length = 5 ∧
    Represents (fun i j : Fin 12 => decide (i ≠ j)) circuit := by
  refine ⟨?_,by decide,by decide,?_⟩
  · have ports : circuit.gates.all (fun g =>
        (match g.op with | .and | .or => true | _ => false) && decide (g.inputs.length ≤ 2)) := by decide
    intro g hg
    have h := List.all_eq_true.mp ports g hg
    cases h₁ : g.op <;> simp_all
  · have check : ∀ i j : Fin 12, formula i j = decide (i ≠ j) := by decide
    intro i j
    exact (eval_formula i j).trans (check i j)

#print axioms grid_upper
end CrownGrid
