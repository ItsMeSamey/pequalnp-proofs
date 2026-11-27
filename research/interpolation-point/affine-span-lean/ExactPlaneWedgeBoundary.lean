import Mathlib.LinearAlgebra.LinearPMap
import Mathlib.LinearAlgebra.Basis.VectorSpace
namespace ExactPlaneWedgeBoundary
variable {F K B : Type*} [Field F] [AddCommGroup K] [Module F K]
  [AddCommGroup B] [Module F B]

def leftBoundary (L R E : Submodule F K) := L ⊓ (R ⊔ E)
def rightBoundary (L R E : Submodule F K) := R ⊓ (L ⊔ E)
def parentBoundary (L R E : Submodule F K) := (L ⊔ R) ⊓ E

theorem overlap_left (L R E : Submodule F K) : L ⊓ R ≤ leftBoundary L R E :=
  inf_le_inf_left L le_sup_left
theorem overlap_right (L R E : Submodule F K) : L ⊓ R ≤ rightBoundary L R E :=
  le_inf inf_le_right (inf_le_left.trans le_sup_left)

theorem parts {L R E : Submodule F K} {a b : K} (ha : a∈L) (hb : b∈R)
    (outside : a+b∈E) : a∈leftBoundary L R E ∧ b∈rightBoundary L R E := by
  have subA : a+b∈R⊔E := (le_sup_right : E≤R⊔E) outside
  have subB : a+b∈L⊔E := (le_sup_right : E≤L⊔E) outside
  exact ⟨⟨ha,by simpa using (R⊔E).sub_mem subA ((le_sup_left : R≤R⊔E) hb)⟩,
    ⟨hb,by simpa using (L⊔E).sub_mem subB ((le_sup_left : L≤L⊔E) ha)⟩⟩

theorem parent_parts (L R E : Submodule F K) (x : parentBoundary L R E) :
    ∃ a : leftBoundary L R E, ∃ b : rightBoundary L R E, (a:K)+(b:K)=x := by
  obtain ⟨a,ha,b,hb,eq⟩ := Submodule.mem_sup.mp x.property.1
  obtain ⟨ac,bc⟩ := parts (E:=E) ha hb (by rw [eq]; exact x.property.2)
  exact ⟨⟨a,ac⟩,⟨b,bc⟩,eq⟩

theorem glue (L R : Submodule F K) (f : L →ₗ[F] B) (g : R →ₗ[F] B)
    (agree : ∀ x : ↥(L⊓R), f ⟨x.val,x.property.1⟩=g ⟨x.val,x.property.2⟩) :
    ∃ h : ↥(L⊔R) →ₗ[F] B, ∀ (a : L) (b : R) (z : ↥(L⊔R)),
        (a:K)+(b:K)=z → h z=f a+g b := by
  let l : K →ₗ.[F] B := ⟨L,f⟩
  let r : K →ₗ.[F] B := ⟨R,g⟩
  have ok : ∀ (a : l.domain) (b : r.domain), (a:K)=b → l a=r b := by
    rintro ⟨a,ha⟩ ⟨b,hb⟩ eq
    change a=b at eq
    subst b
    exact agree ⟨a,ha,hb⟩
  exact ⟨(l.sup r ok).toFun, fun a b z eq => LinearPMap.sup_apply ok a b z eq⟩

theorem parent_determined (L R E : Submodule F K) (h h' : ↥(L⊔R) →ₗ[F] B)
    (left : ∀ a : leftBoundary L R E,
        h ⟨a.val,(le_sup_left : L≤L⊔R) a.property.1⟩=h' ⟨a.val,(le_sup_left : L≤L⊔R) a.property.1⟩)
    (right : ∀ b : rightBoundary L R E,
        h ⟨b.val,(le_sup_right : R≤L⊔R) b.property.1⟩=h' ⟨b.val,(le_sup_right : R≤L⊔R) b.property.1⟩)
    (x : parentBoundary L R E) :
    h ⟨x.val,x.property.1⟩=h' ⟨x.val,x.property.1⟩ := by
  obtain ⟨a,b,eq⟩ := parent_parts L R E x
  let u : ↥(L⊔R) := ⟨a.val,(le_sup_left : L≤L⊔R) a.property.1⟩
  let v : ↥(L⊔R) := ⟨b.val,(le_sup_right : R≤L⊔R) b.property.1⟩
  have z : u+v=⟨x.val,x.property.1⟩ := Subtype.ext eq
  rw [←z,map_add,map_add]
  exact congrArg₂ (·+·) (left a) (right b)

theorem partial_sum_iff {L R E : Submodule F K} {a b : K} (ha : a∈L) (hb : b∈R) :
    a+b∈parentBoundary L R E ↔
      a∈leftBoundary L R E ∧ b∈rightBoundary L R E ∧ a+b∈E := by
  constructor
  · intro h
    exact ⟨(parts ha hb h.2).1,(parts ha hb h.2).2,h.2⟩
  · rintro ⟨_,_,ext⟩
    exact ⟨Submodule.mem_sup.mpr ⟨a,ha,b,hb,rfl⟩,ext⟩

#print axioms glue
#print axioms parent_determined
#print axioms partial_sum_iff
end ExactPlaneWedgeBoundary
