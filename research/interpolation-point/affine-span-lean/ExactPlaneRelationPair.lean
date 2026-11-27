import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.LinearAlgebra.Dimension.Constructions
import ExactPlaneFirstRelation
import ExactPlaneResidualPivots
import ExactPlanePhysicalResidual
namespace ExactPlaneRelationPair
open ExactPlaneFirstRelation ExactPlanePhysicalConverse ExactPlaneResidualPivots
open scoped BigOperators
variable {I K H : Type*} [Fintype I] [DecidableEq I]
variable [AddCommGroup K] [Module (ZMod 2) K] [AddCommGroup H] [Module (ZMod 2) H]

theorem from_gain (k : I→K) (b : I→Plane) (h : I→H) (A : Finset I)
    (g : K→ₗ[ZMod 2] Plane) (mt : ∀i∈A,g (k i)=b i) (y : H)
    (mem : (0,0,y)∈physicalSpan k b h A) :
    ∃ u∈relation k b g,support u⊆A ∧ aggregate h u=y := by
  classical
  have sets : physicalSpan k b h A=ExactPlanePhysicalResidual.indexedSpan A (fun i=>(k i,b i,h i)) := by
    unfold physicalSpan ExactPlanePhysicalResidual.indexedSpan
    congr 1
    ext v
    constructor
    · rintro ⟨i,rfl⟩; exact ⟨i.val,i.property,rfl⟩
    · rintro ⟨i,hi,rfl⟩; exact ⟨⟨i,hi⟩,rfl⟩
  rw [sets] at mem
  obtain ⟨C,sub,eq⟩ := (ExactPlanePhysicalResidual.physical_support A (fun i=>(k i,b i,h i)) _).mp mem
  refine ⟨mask C,(mem_relation _ _ _ _).mpr ⟨?_,?_⟩,by simpa only [support_mask] using sub,?_⟩
  · have first := congrArg Prod.fst eq
    simpa only [aggregate_support,support_mask,Prod.fst_sum] using first
  · intro i hi; exact mt i (sub (support_mask C ▸ hi))
  · have gain := congrArg (fun a : K×Plane×H=>a.2.2) eq
    simpa only [aggregate_support,support_mask,Prod.snd_sum] using gain

theorem into_gain (k : I→K) (b : I→Plane) (h : I→H) (A : Finset I)
    (g : K→ₗ[ZMod 2] Plane) (u : I→ZMod 2) (rel : u∈relation k b g) (sub : support u⊆A) :
    ((0:K),0,aggregate h u)∈physicalSpan k b h A := by
  classical
  obtain ⟨zero,mt⟩ := (mem_relation _ _ _ _).mp rel
  rw [aggregate_support] at zero ⊢
  have tag : (∑ i∈support u,b i)=0 := by
    calc
      _ = ∑ i∈support u,g (k i) := Finset.sum_congr rfl (fun i hi=>(mt i hi).symm)
      _ = _ := by rw [←map_sum,zero,map_zero]
  have eq : (∑ i∈support u,(k i,b i,h i))=((0:K),0,∑ i∈support u,h i) := by
    apply Prod.ext
    · simpa only [Prod.fst_sum] using zero
    · apply Prod.ext <;> simp [Prod.snd_sum,Prod.fst_sum,tag]
  rw [←eq]
  exact (physicalSpan k b h A).sum_mem (fun i hi=>Submodule.subset_span ⟨⟨i,sub hi⟩,rfl⟩)

theorem full_of_gain (k : I→K) (b : I→Plane) (h : I→H) (A : Finset I)
    (g : K→ₗ[ZMod 2] Plane) (mt : ∀i∈A,g (k i)=b i)
    (all : ∀ y : H,((0:K),0,y)∈physicalSpan k b h A) : ExactTrace k b h A := by
  let diff : K×(Plane×H) →ₗ[ZMod 2] Plane :=
    (LinearMap.fst (ZMod 2) Plane H).comp (LinearMap.snd (ZMod 2) K (Plane×H)) -
    g.comp (LinearMap.fst (ZMod 2) K (Plane×H))
  have safe : physicalSpan k b h A ≤ LinearMap.ker diff := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact sub_eq_zero.mpr (mt i.val i.property).symm
  intro z y
  constructor
  · intro hz
    have h' : z-g 0=0 := safe hz
    simpa using h'
  · rintro rfl; exact all y

theorem pair_trace (k : I→K) (b h : I→Plane) (A : Finset I)
    (g : K→ₗ[ZMod 2] Plane) (mt : ∀i∈A,g (k i)=b i)
    (u v : I→ZMod 2) (ru : u∈relation k b g) (rv : v∈relation k b g)
    (su : support u⊆A) (sv : support v⊆A)
    (ind : Independent (aggregate h u) (aggregate h v)) : ExactTrace k b h A := by
  apply full_of_gain k b h A g mt
  let vert : Plane→ₗ[ZMod 2] K×(Plane×Plane) :=
    (0 : Plane→ₗ[ZMod 2] K).prod ((0 : Plane→ₗ[ZMod 2] Plane).prod LinearMap.id)
  let rows : Fin 2→Plane := fun i=>if i=0 then aggregate h u else aggregate h v
  have top := ind.span_eq_top_of_card_eq_finrank
    (by simp [Plane,Module.finrank_prod] : Fintype.card (Fin 2)=Module.finrank (ZMod 2) Plane)
  change Submodule.span (ZMod 2) (Set.range rows)=⊤ at top
  have le : Submodule.span (ZMod 2) (Set.range rows) ≤ (physicalSpan k b h A).comap vert := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i,rfl⟩
    change ((0:K),0,rows i)∈physicalSpan k b h A
    by_cases hi : i=0
    · simpa only [rows,if_pos hi] using into_gain k b h A g u ru su
    · simpa only [rows,if_neg hi] using into_gain k b h A g v rv sv
  rw [top] at le
  exact fun y=>le (Submodule.mem_top)

theorem exact_pair (k : I→K) (b h : I→Plane) (A : Finset I) :
    ExactTrace k b h A ↔ ∃ (g : K→ₗ[ZMod 2] Plane) (u v : I→ZMod 2),
      (∀i∈A,g (k i)=b i) ∧ u∈relation k b g ∧ v∈relation k b g ∧
      support u⊆A ∧ support v⊆A ∧ Independent (aggregate h u) (aggregate h v) := by
  constructor
  · intro tr
    obtain ⟨g,mt⟩ := ExactPlanePhysicalConverse.chart k b h A tr
    obtain ⟨u,ru,su,hu⟩ := from_gain k b h A g mt (1,0) ((tr 0 _).mpr rfl)
    obtain ⟨v,rv,sv,hv⟩ := from_gain k b h A g mt (0,1) ((tr 0 _).mpr rfl)
    refine ⟨g,u,v,mt,ru,rv,su,sv,?_⟩
    rw [hu,hv]
    exact (det_ne_iff _ _).mp (by decide)
  · rintro ⟨g,u,v,mt,ru,rv,su,sv,ind⟩
    exact pair_trace k b h A g mt u v ru rv su sv ind
#print axioms exact_pair
end ExactPlaneRelationPair
