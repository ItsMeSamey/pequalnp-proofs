import ExactPlaneWedgeProduct
import Mathlib.Data.Finset.Sort
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Data.Fin.Tuple.Basic
namespace ExactPlaneWedgeLayout
open ExactPlaneWedgeProduct
def dim (n : ℕ) := (n+(n+n.choose 2))+1
theorem dim_eq (n : ℕ) : dim n=1+2*n+n.choose 2 := by unfold dim; omega

private instance pairOrd (n : ℕ) : LinearOrder (Pair n) :=
  LinearOrder.lift' (fun p => finProdFinEquiv p.val)
    (fun _ _ h => Subtype.ext (finProdFinEquiv.injective h))

theorem pair_count (n : ℕ) : Fintype.card (Pair n) = n.choose 2 := by
  rw [Fintype.card_subtype]
  simpa using (Fintype.card_product_filter_lt (α:=Fin n))

private def before (p q : Pair n) : Prop := finProdFinEquiv p.val ≤ finProdFinEquiv q.val
private instance : DecidableRel (@before n) := fun p q => inferInstanceAs (Decidable (finProdFinEquiv p.val ≤ finProdFinEquiv q.val))
private instance : Std.Total (@before n) := ⟨fun p q => le_total _ _⟩
private instance : IsTrans (Pair n) before := ⟨fun _ _ _ => le_trans⟩
private instance : Std.Antisymm (@before n) := ⟨fun _ _ a b => Subtype.ext (finProdFinEquiv.injective (le_antisymm a b))⟩

def pairList (n : ℕ) : List (Pair n) := (Finset.univ : Finset (Pair n)).sort before
theorem pairList_length (n : ℕ) : (pairList n).length=n.choose 2 := by
  simp [pairList,pair_count]

def pairAt (n : ℕ) (j : Fin (n.choose 2)) : Pair n :=
  (pairList n).get (Fin.cast (pairList_length n).symm j)

theorem pairAt_surjective (n : ℕ) : Function.Surjective (pairAt n) := by
  intro p
  have mem : p∈pairList n := by simp [pairList]
  obtain ⟨i,eq⟩ := List.mem_iff_get.mp mem
  exact ⟨Fin.cast (pairList_length n) i,by simpa [pairAt] using eq⟩

private def scalar (n : ℕ) : Feature n →ₗ[F] F := LinearMap.fst _ _ _
private def first (n : ℕ) : Feature n →ₗ[F] V n :=
  (LinearMap.fst _ _ _).comp (LinearMap.snd _ _ _)
private def second (n : ℕ) : Feature n →ₗ[F] V n :=
  (LinearMap.fst _ _ _).comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))
private def minors (n : ℕ) : Feature n →ₗ[F] Alt n :=
  (LinearMap.snd _ _ _).comp ((LinearMap.snd _ _ _).comp (LinearMap.snd _ _ _))

def slot (n : ℕ) : Fin (dim n) → Feature n →ₗ[F] F :=
  Fin.cases (scalar n) (Fin.addCases (fun i => (LinearMap.proj i).comp (first n))
    (Fin.addCases (fun i => (LinearMap.proj i).comp (second n))
      (fun j => (LinearMap.proj (pairAt n j)).comp (minors n))))

def flatten (n : ℕ) : Feature n →ₗ[F] V (dim n) := LinearMap.pi (slot n)

theorem flatten_injective (n : ℕ) : Function.Injective (flatten n) := by
  intro x y h
  have agree (j : Fin (dim n)) : slot n j x=slot n j y := congrFun h j
  refine Prod.ext (by simpa [slot,scalar,dim] using agree (0 : Fin ((n+(n+n.choose 2))+1))) (Prod.ext (funext fun i => ?_) (Prod.ext (funext fun i => ?_)
    (funext fun ij => ?_)))
  · simpa [slot,first] using agree (Fin.castAdd (n+n.choose 2) i).succ
  · simpa [slot,second] using agree (Fin.natAdd n (Fin.castAdd (n.choose 2) i)).succ
  · obtain ⟨j,rfl⟩ := pairAt_surjective n ij
    simpa [slot,minors] using agree (Fin.natAdd n (Fin.natAdd n j)).succ

def store (n : ℕ) (f : Feature n) : Vector F (dim n) := Vector.ofFn (flatten n f)
@[simp] theorem store_get (n : ℕ) (f : Feature n) (j : Fin (dim n)) :
    (store n f)[j]=flatten n f j := by simp [store]

#print axioms flatten_injective
end ExactPlaneWedgeLayout
