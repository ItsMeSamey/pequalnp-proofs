import ThresholdReceiverShield
namespace ThresholdSecondaryReceivers
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open T2SoleOrSplice T2CubeDeletion T2RegularOrDelete T2OrPartition ThresholdSimpleIncidence
open ThresholdSharedFlow ThresholdStarBypass ResidualSurplus

theorem forbid_parallel {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (ne : x≠y) (u v z : Id (source gs out))
    (H : Finset (Id (source gs out))) (ug : u∈good (source gs out) n H)
    (ux : u∈endpoints (layout n gs out M.eligible) x)
    (zx : z∈endpoints (layout n gs out M.eligible) x)
    (vy : v∈endpoints (layout n gs out M.eligible) y)
    (py : endpoints (layout n gs out M.eligible) y⊆{v,z})
    (subset : signature (source gs out) n v ⊆ signature (source gs out) n u) : False := by
  let L := layout n gs out M.eligible
  apply ThresholdReceiverShield.cannot_add_shield M reg x y ne {v} (Finset.singleton_subset_iff.mpr vy)
  · intro w hw i hi s xs
    obtain rfl := Finset.mem_singleton.mp hw
    have hot := (receiver_later L ug (subset hi)).2
    exact ThresholdSharedPairErase.probe_le_actual L u
      (fun k => ((source gs out).wires (vector s)).getD k false)
      (fun k => (L.atIndex k).eval _ (by simp [vector])) (endpoint_hot L s x u xs ux) _ hot
  · intro i hi skip
    have iz := (Finset.mem_insert.mp (py hi)).resolve_left (by simpa using skip)
    obtain rfl := Finset.mem_singleton.mp iz
    exact endpoint_hot L {x} x _ (by simp) zx

theorem signatures_injective {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (H : Finset (Id (source gs out)))
    (common : ∀ u∈H, ∀ v∈H, u≠v → ∃ z x y, x≠y ∧
       u∈endpoints (layout n gs out M.eligible) x ∧ z∈endpoints (layout n gs out M.eligible) x ∧
       v∈endpoints (layout n gs out M.eligible) y ∧ endpoints (layout n gs out M.eligible) y⊆{v,z}) :
    Set.InjOn (signature (source gs out) n) (↑(good (source gs out) n H)) := by
  intro u hu v hv eq
  by_contra ne
  obtain ⟨z,x,y,xy,ux,zx,vy,py⟩ := common u (Finset.mem_filter.mp hu).1 v (Finset.mem_filter.mp hv).1 ne
  exact forbid_parallel M reg x y xy u v z H hu ux zx vy py eq.ge
end ThresholdSecondaryReceivers
