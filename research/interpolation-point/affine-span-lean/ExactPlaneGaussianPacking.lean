import ExactPlaneFiveQueries
import Mathlib.Data.Fin.Tuple.Basic
import Mathlib.Tactic.FinCases

namespace ExactPlaneGaussianPacking
open ExactPlanePhysicalConverse ExactPlaneFiveQueries
variable {d : ℕ}
abbrev Key (d : ℕ) := Fin d → F

def low (v : V (Key d)) : Fin 4 → F := ![v.2.2.2,v.2.2.1,v.2.1.2,v.2.1.1]

def pack : V (Key d) →ₗ[F] Key (d+4) where
  toFun v := Fin.append v.1 (low v)
  map_add' x y := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · fin_cases j <;> simp [low]
  map_smul' c x := by
    funext i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp
    · fin_cases j <;> simp [low]

theorem pack_injective : Function.Injective (pack (d:=d)) := by
  intro x y h
  change Fin.append x.1 (low x) = Fin.append y.1 (low y) at h
  have fields (j : Fin 4) := congrFun h (Fin.natAdd d j)
  simp only [Fin.append_right] at fields
  refine Prod.ext (funext fun i => ?_) (Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_))
  · simpa only [Fin.append_left] using congrFun h (Fin.castAdd 4 i)
  · exact fields 3
  · exact fields 2
  · exact fields 1
  · exact fields 0

theorem pack_span {I : Type*} (A : Finset I) (k : I → Key d) (b h : I → P)
    (y : V (Key d)) :
    pack y ∈ Submodule.span F ((fun i => pack (k i,b i,h i)) '' (A : Set I)) ↔
      y ∈ physicalSpan k b h A := by
  classical
  let C := Set.range (fun i : ↥A => (k i.val,b i.val,h i.val))
  have family : (fun i => pack (k i,b i,h i)) '' (A : Set I) = pack '' C := by
    ext z
    constructor
    · rintro ⟨i,hi,rfl⟩
      exact ⟨_,⟨⟨i,hi⟩,rfl⟩,rfl⟩
    · rintro ⟨_,⟨i,rfl⟩,rfl⟩
      exact ⟨i.val,i.property,rfl⟩
  rw [family,← Submodule.map_span]
  constructor
  · rintro ⟨v,hv,eq⟩
    exact pack_injective eq ▸ hv
  · intro hy
    exact ⟨y,hy,rfl⟩

#print axioms pack_span
end ExactPlaneGaussianPacking
