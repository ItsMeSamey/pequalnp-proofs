import ExactPlaneRelationPair
import ExactPlaneForcedLine
namespace ExactPlaneFirstRank
open ExactPlaneFirstRelation ExactPlaneRelationPair ExactPlanePhysicalConverse ExactPlaneResidualPivots
open scoped BigOperators
variable {I K : Type*} [Fintype I] [DecidableEq I] [AddCommGroup K] [Module (ZMod 2) K]

def scalar (h : I→Plane) (u : I→ZMod 2) : I→ZMod 2 := fun i=>det (aggregate h u) (h i)

def detMap (w : Plane) : Plane →ₗ[ZMod 2] ZMod 2 where
  toFun := det w
  map_add' := by intro x y; simp [det,mul_add,add_mul]; ring
  map_smul' := by intro c x; simp [det,smul_eq_mul]; ring

theorem scalar_value (h : I→Plane) (u v : I→ZMod 2) :
    aggregate (scalar h u) v=det (aggregate h u) (aggregate h v) := by
  simp only [aggregate_support (scalar h u),aggregate_support h v]
  change (∑ i∈support v,detMap (aggregate h u) (h i))=detMap (aggregate h u) _
  rw [map_sum]

theorem private_zero (k : I→K) (b : I→Plane) : first k b ≤ LinearMap.ker (aggregate k) := by
  apply iSup_le
  intro g u hu
  exact ((mem_relation _ _ _ _).mp hu).1

theorem scalar_certificate (k : I→K) (b h : I→Plane) (u : I→ZMod 2) (hu : u∈first k b)
    (A : Finset I) (inside : support u⊆A) :
    ExactTrace k b (scalar h u) A ↔
      ∃ (g : K→ₗ[ZMod 2] Plane) (v : I→ZMod 2), Match g k b A ∧
        u∈relation k b g ∧ v∈relation k b g ∧ support v⊆A ∧
        Independent (aggregate h u) (aggregate h v) := by
  constructor
  · intro tr
    obtain ⟨g,mt⟩ := ExactPlanePhysicalConverse.chart k b (scalar h u) A tr
    obtain ⟨v,rv,sv,one⟩ := from_gain k b (scalar h u) A g mt 1 ((tr 0 1).mpr rfl)
    refine ⟨g,v,mt,(mem_relation _ _ _ _).mpr ⟨private_zero k b hu,fun i hi=>mt i (inside hi)⟩,rv,sv,?_⟩
    rw [scalar_value] at one
    exact (det_ne_iff _ _).mp (by rw [one]; decide)
  · rintro ⟨g,v,mt,_,rv,sv,ind⟩
    have nz := (det_ne_iff _ _).mpr ind
    rw [←scalar_value] at nz
    have bit : ∀ a : ZMod 2,a=0 ∨ a=1 := by decide
    have eq := (bit _).resolve_left nz
    have good := into_gain k b (scalar h u) A g v rv sv
    rw [eq] at good
    apply full_of_gain k b (scalar h u) A g mt
    intro y
    rcases bit y with rfl|rfl
    · exact (physicalSpan k b (scalar h u) A).zero_mem
    · exact good

theorem forced (k : I→K) (b h : I→Plane) :
    (∃ A : Finset I,ExactTrace k b h A) ↔
      ∃ u∈first k b, aggregate h u≠0 ∧ ∃ R : Finset I,Disjoint R (support u) ∧
        ExactPlaneForcedLine.QTrace k b (scalar h u) (support u) R := by
  constructor
  · rintro ⟨A,tr⟩
    obtain ⟨g,u,v,mt,ru,rv,su,sv,ind⟩ := (exact_pair k b h A).mp tr
    have hu : u∈first k b := (le_iSup (relation k b) g) ru
    have nz : aggregate h u≠0 := by
      intro zero
      have ne := (det_ne_iff _ _).mpr ind
      simp [zero,det] at ne
    exact ⟨u,hu,nz,(ExactPlaneForcedLine.forced_iff k b (scalar h u) (support u)).mp
      ⟨A,su,(scalar_certificate k b h u hu A su).mpr ⟨g,v,mt,ru,rv,sv,ind⟩⟩⟩
  · rintro ⟨u,hu,_,R,_,qr⟩
    have tr := (ExactPlaneForcedLine.union_iff k b (scalar h u) (support u) R).mpr qr
    have sub : support u⊆support u∪R := Finset.subset_union_left
    obtain ⟨g,v,mt,ru,rv,sv,ind⟩ := (scalar_certificate k b h u hu _ sub).mp tr
    exact ⟨_,pair_trace k b h _ g mt u v ru rv sub sv ind⟩

theorem original_union (k : I→K) (b h : I→Plane) (u : I→ZMod 2) (hu : u∈first k b)
    (R : Finset I) (qr : ExactPlaneForcedLine.QTrace k b (scalar h u) (support u) R) :
    ExactTrace k b h (support u∪R) := by
  have sub : support u⊆support u∪R := Finset.subset_union_left
  have tr := (ExactPlaneForcedLine.union_iff k b (scalar h u) (support u) R).mpr qr
  obtain ⟨g,v,mt,ru,rv,sv,ind⟩ := (scalar_certificate k b h u hu _ sub).mp tr
  exact pair_trace k b h _ g mt u v ru rv sub sv ind
#print axioms forced
#print axioms original_union
end ExactPlaneFirstRank
