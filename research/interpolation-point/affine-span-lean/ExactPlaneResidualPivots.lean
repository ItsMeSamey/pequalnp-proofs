import ExactPlaneDeterminant
namespace ExactPlaneResidualPivots
open ExactPlaneAffineSubstitution
abbrev Plane := F × F
def det (u v : Plane) : F := u.1*v.2+v.1*u.2
def Independent (u v : Plane) := LinearIndependent F (fun i : Fin 2 => if i=0 then u else v)
theorem det_ne_iff (u v : Plane) : det u v≠0 ↔ Independent u v := by
  have t := ExactPlaneDeterminant.score_ne_iff
    (J:=Fin 0) (fun _=>u.1) (fun _=>v.1) (fun _=>u.2) (fun _=>v.2) 0
  simpa only [det,Independent,ExactPlaneDeterminant.independent,ExactPlaneDeterminant.score,
    Prod.mk.eta] using t

theorem pivots {E : Type*} (active : Finset E) (res : E→Plane) {u v : Plane}
    (hu : u∈Submodule.span F (res '' (active : Set E)))
    (hv : v∈Submodule.span F (res '' (active : Set E))) (hi : Independent u v) :
    ∃ e∈active,∃ f∈active,Independent (res e) (res f) := by
  classical
  by_contra! none
  apply (det_ne_iff u v).mpr hi
  apply Submodule.span_induction₂ (p:=fun x y _ _ => det x y=0) _ _ _ _ _ _ _ hu hv
  · rintro _ _ ⟨e,he,rfl⟩ ⟨f,hf,rfl⟩
    exact not_ne_iff.mp (fun nz => none e he f hf ((det_ne_iff _ _).mp nz))
  · intro y _; simp [det]
  · intro x _; simp [det]
  · intro x y z _ _ _ hx hy
    calc det (x+y) z = det x z + det y z := by simp [det,add_mul] <;> ring
         _ = 0 := by rw [hx,hy,add_zero]
  · intro x y z _ _ _ hy hz
    calc det x (y+z) = det x y + det x z := by simp [det,mul_add] <;> ring
         _ = 0 := by rw [hy,hz,add_zero]
  · intro a x y _ _ hx
    calc det (a • x) y = a*det x y := by simp [det] <;> ring
         _ = 0 := by rw [hx,mul_zero]
  · intro a x y _ _ hy
    calc det x (a • y) = a*det x y := by simp [det] <;> ring
         _ = 0 := by rw [hy,mul_zero]
#print axioms pivots
end ExactPlaneResidualPivots
