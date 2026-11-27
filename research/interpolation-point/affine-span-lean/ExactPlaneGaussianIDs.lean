import ExactPlaneGaussian
import ExactPlaneGaussianPacking
import ExactPlaneGaussianBasisBound
import Mathlib.Data.Finset.Sort
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
namespace ExactPlaneGaussianIDs
open ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneGaussianPacking
open Submodule
variable {d N : ℕ}
abbrev col (k : Fin N → Key d) (b h : Fin N → Plane) (i : Fin N) := (k i,b i,h i)
def walk (v : Fin N → Key d) : List (Fin N) →
    ExactPlaneGaussian.Bank d (Fin N) × Finset (Fin N)
  | [] => ([],∅)
  | i::xs =>
    let prev := walk v xs
    let residual := ExactPlaneGaussian.reduce prev.1 (v i,0)
    (ExactPlaneGaussian.insert prev.1 (v i,Pi.single i 1),
      if residual.1=0 then prev.2 else insert i prev.2)

theorem bank (v : Fin N → Key d) (xs : List (Fin N)) :
    (walk v xs).1=ExactPlaneGaussian.build v xs := by
  induction xs with
  | nil => rfl
  | cons i xs ih => simp [walk,ExactPlaneGaussian.build,ih]

private theorem phys (k : Fin N → Key d) (b h : Fin N → Plane) (A : Finset (Fin N)) :
    physicalSpan k b h A = span F (col k b h '' (A : Set (Fin N))) := by
  unfold physicalSpan
  congr 1
  ext x
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨i.val,i.property,rfl⟩
  · rintro ⟨i,hi,rfl⟩
    exact ⟨⟨i,hi⟩,rfl⟩

theorem walk_spec (k : Fin N → Key d) (b h : Fin N → Plane) (xs : List (Fin N)) :
    let T := (walk (fun i => pack (col k b h i)) xs).2
    T ⊆ xs.toFinset ∧ LinearIndepOn F (col k b h) (T : Set (Fin N)) ∧
    physicalSpan k b h T=physicalSpan k b h xs.toFinset := by
  classical
  let v := fun i => pack (col k b h i)
  induction xs with
  | nil => exact ⟨by simp [walk],by simpa [walk] using linearIndepOn_empty F (col k b h),rfl⟩
  | cons i xs ih =>
    let T := (walk v xs).2
    obtain ⟨sub,ind,same⟩ := ih
    let r := ExactPlaneGaussian.reduce (walk v xs).1 (v i,0)
    have test : r.1=0 ↔ col k b h i ∈ physicalSpan k b h xs.toFinset := by
      rw [←pack_span,←ExactPlaneGaussian.solve_hits xs v (v i)]
      by_cases eq : r.1=0 <;> simp_all [ExactPlaneGaussian.solve,r,bank]
    change (if r.1=0 then T else insert i T) ⊆ _ ∧
      LinearIndepOn F (col k b h) (((if r.1=0 then T else insert i T) : Finset (Fin N)) : Set (Fin N)) ∧
      physicalSpan k b h (if r.1=0 then T else insert i T)=_
    by_cases hz : r.1=0
    · simp only [hz,ite_true,List.toFinset_cons]
      refine ⟨fun j hj => Finset.mem_insert_of_mem (sub hj),ind,?_⟩
      rw [same,phys,phys,Finset.coe_insert,Set.image_insert_eq]
      exact (Submodule.span_insert_eq_span (phys k b h _ ▸ test.mp hz)).symm
    · simp only [hz,ite_false,List.toFinset_cons]
      refine ⟨Finset.insert_subset_insert i sub,?_,?_⟩
      · rw [Finset.coe_insert]
        apply ind.insert
        rw [←phys,same]
        exact fun bad => hz (test.mpr bad)
      · have same' := same
        rw [phys,phys] at same'
        simp only [phys,Finset.coe_insert,Set.image_insert_eq,Submodule.span_insert]
        rw [same']

def basis (A : Finset (Fin N)) (k : Fin N → Key d) (b h : Fin N → Plane) :=
  (walk (fun i => pack (col k b h i)) (A.sort (·≤·))).2

theorem keep_spec (A : Finset (Fin N)) (k : Fin N → Key d) (b h : Fin N → Plane) :
    basis A k b h ⊆ A ∧ LinearIndependent F (fun i : ↥(basis A k b h) =>
      (k i.val,b i.val,h i.val)) ∧ physicalSpan k b h (basis A k b h)=physicalSpan k b h A := by
  obtain ⟨sub,ind,same⟩ := walk_spec k b h (A.sort (·≤·))
  rw [Finset.sort_toFinset] at sub same
  refine ⟨sub,?_,same⟩
  let T := basis A k b h
  change LinearIndepOn F (col k b h) (T : Set (Fin N)) at ind
  let embed : (↥T) → ↥(T : Set (Fin N)) := fun i => ⟨i.val,i.property⟩
  exact (show LinearIndependent F (fun j : ↥(T : Set (Fin N)) => col k b h j.val) from ind).comp embed (fun i j eq => Subtype.ext (congrArg Subtype.val eq))

theorem basis_spec (A : Finset (Fin N)) (k : Fin N → Key d) (b h : Fin N → Plane)
    (yes : ExactTrace k b h A) :
    basis A k b h ⊆ A ∧ ExactTrace k b h (basis A k b h) ∧
    (basis A k b h).card≤Module.finrank F (ExactPlaneObservedSpan.observed k)+2 := by
  obtain ⟨sub,ind,same⟩ := keep_spec A k b h
  exact ⟨sub,ExactPlaneGaussianBasisBound.bound k b h A _ yes ind same⟩

def rank (A : Finset (Fin N)) (k : Fin N → Key d) (b h : Fin N → Plane) :=
  (basis A k b h).card

theorem rank_eq (A : Finset (Fin N)) (k : Fin N → Key d) (b h : Fin N → Plane) :
    rank A k b h=Module.finrank F (physicalSpan k b h A) := by
  let T := basis A k b h
  obtain ⟨_,ind,same⟩ := keep_spec A k b h
  rw [←same]
  change T.card=Module.finrank F (span F (Set.range (fun i : ↥T => (k i.val,b i.val,h i.val))))
  rw [finrank_span_eq_card (b:=fun i : ↥T => (k i.val,b i.val,h i.val)) ind,Fintype.card_coe]

#print axioms rank_eq
#print axioms basis_spec
end ExactPlaneGaussianIDs
