import ExactPlaneWedgeRun
import ExactPlaneWedgePlanPhysical
namespace ExactPlaneWedgeRun
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgePlan ExactPlaneWedgeArrayDP
open ExactPlaneWedgeTree ExactPlaneWedgeDecision ExactPlaneResidualPivots ExactPlanePhysicalWedgeTree
open ExactPlanePhysicalConverse (ExactTrace)
open ExactPlaneFeatureStream (selectFeatures)
open ExactPlaneWedgePlanPhysical
variable {d n : Nat}

private theorem root_unique (k : Fin n→Word d) (t : Indexed d n)
    (s : ExactPlaneWedgeSplit.State (boundary k t ⊥) Plane) : s=rootState k (tree t) := by
  have z (x : boundary k t ⊥) : x=0 := Subtype.ext ((Submodule.mem_bot _).mp x.property.2)
  cases s with
  | mk g p q =>
    have gz : g=0 := LinearMap.ext fun x => by rw [z x]; simp
    rw [gz,z p,z q]
    rfl

theorem physical (t : Indexed d n) (k : Fin n→Word d) (b h : Fin n→Plane)
    (sep : separated (tree t)) (cover : leaves (tree t)=Finset.univ) (valid : Valid k t ⊥) :
    (∀ uv,solve t k b h=some uv → Good k b h uv.1 uv.2 ∧ ExactTrace k b h (uv.1∪uv.2)) ∧
    (solve t k b h≠none ↔ ∃ A,ExactTrace k b h A) := by
  obtain ⟨e,he⟩ := valid_here k t ⊥ valid
  let j := first (cut t)
  have eq := ExactPlaneWedgePlanPhysical.exact k b t sep ⊥ valid e he j
  rw [root_unique k t (ExactPlaneWedgeCodecState.decode e (stateVector (cut t))[j])] at eq
  have cert := ExactPlaneWedgeArrayDP.exact selectFeatures select_law (plan (physicalRows k b) t) j
  rw [eq] at cert
  have ans := retained k b h (tree t) cover (rows t k b) (fun _ hx=>cert.1 hx) cert.2
  exact ⟨fun uv ok=>⟨ans.1 uv ok,good_trace k b h _ _ (ans.1 uv ok)⟩,ans.2⟩
#print axioms physical
end ExactPlaneWedgeRun
