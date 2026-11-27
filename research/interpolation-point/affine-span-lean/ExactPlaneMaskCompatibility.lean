import ExactPlanePairSearch
import ExactPlaneFiveQueries
namespace ExactPlaneMaskCompatibility
open ExactPlanePhysicalConverse ExactPlaneFirstRelation ExactPlaneResidualPivots ExactPlaneRelationPair
open ExactPlanePairSearch (Key)
variable {N d : Nat}
abbrev Id (N : Nat) := Fin N ⊕ Bool
def augKey (k : Fin N→Key d) : Id N→Key d := Sum.elim k (fun _=>0)
def augTag (b : Fin N→Plane) : Id N→Plane := Sum.elim b (fun _=>0)
def augGain : Id N→Plane := Sum.elim (fun _=>0) (fun side=>if side then (0,1) else (1,0))
def ids (U : Finset (Fin N)) : List (Id N) :=
  (U.sort (·≤·)).map Sum.inl ++ [Sum.inr false,Sum.inr true]
def test (k : Fin N→Key d) (b : Fin N→Plane) (U : Finset (Fin N)) :=
  ExactPlaneGaussianCandidate.check (ids U) (augKey k) (augTag b) augGain

theorem left_mem (U : Finset (Fin N)) (i : Fin N) :
    Sum.inl i ∈ (ids U).toFinset ↔ i∈U := by simp [ids]

theorem test_iff (k : Fin N→Key d) (b : Fin N→Plane) (U : Finset (Fin N)) :
    test k b U=true ↔ ∃ g : Key d →ₗ[ZMod 2] Plane, Match g k b U := by
  rw [test,ExactPlaneGaussianCandidate.check_iff]
  constructor
  · intro yes
    obtain ⟨g,ok⟩ := ExactPlanePhysicalConverse.chart _ _ _ _ yes
    exact ⟨g,fun i hi=>ok (.inl i) ((left_mem U i).mpr hi)⟩
  · rintro ⟨g,ok⟩
    apply full_of_gain _ _ _ _ g
    · rintro (i|side) mem
      · exact ok i ((left_mem U i).mp mem)
      · exact map_zero g
    · intro y
      let S := physicalSpan (augKey k) (augTag b) augGain (ids U).toFinset
      have base (side : Bool) : ((0:Key d),(0:Plane),augGain (Sum.inr side : Id N))∈S :=
        Submodule.subset_span ⟨⟨Sum.inr side,by cases side <;> simp [ids]⟩,rfl⟩
      have sum := S.add_mem (S.smul_mem y.1 (base false)) (S.smul_mem y.2 (base true))
      change ((0:Key d),(0:Plane),y)∈S
      simpa [augGain,Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul] using sum
#print axioms test_iff
end ExactPlaneMaskCompatibility
