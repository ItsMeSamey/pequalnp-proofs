import ExactPlaneNumericalDual
import ExactPlaneBinaryArithmetic
namespace ExactPlaneQuotientRows
open ExactPlaneFieldSampler ExactPlaneSamplerRank ExactPlaneNumericalRows
open ExactPlaneBinaryArithmetic (Word power encode encode_power)

def seedRows {r : Nat} (m : Nat) (c : Word r) :=
  rows r m (fun x t j=>dot t (power c x j.val))

theorem count {r : Nat} (m : Nat) (c : Word r) : (seedRows m c).length=(2^r)^2 :=
  length_rows _ _ _

theorem complete {P : Polynomial F} (hm : P.Monic) [Fact (Irreducible P)]
    (hr : 0<P.natDegree) (dim : 0<m) (large : m*2^R < 2^P.natDegree) :
    OntoHits (points (seedRows (r:=P.natDegree) m (fun i=>-P.coeff i.val))).toFinset R := by
  classical
  let e := encode hm
  letI : Fintype (AdjoinRoot P) := Fintype.ofEquiv (V P.natDegree) e.toEquiv
  letI : Fintype (D (AdjoinRoot P)) := Fintype.ofEquiv (AdjoinRoot P)
    (Module.finBasis F (AdjoinRoot P)).toDualEquiv.toEquiv
  have card : Fintype.card (AdjoinRoot P) = 2^P.natDegree := by
    rw [← Fintype.card_congr e.toEquiv]
    simp [V,F,ZMod.card]
  exact power_hits e _ (encode_power hm hr) dim (by simpa only [card] using large)

def run {N d r : Nat} (m : Nat) (c : Word r)
    (chart : Vector F m → Vector ExactPlaneResidualPivots.Plane N)
    (keys : Vector (Vector F d) N) (tags heights : Vector ExactPlaneResidualPivots.Plane N) :=
  ExactPlaneNumericalRows.run (seedRows m c) chart keys tags heights

#print axioms complete
end ExactPlaneQuotientRows
