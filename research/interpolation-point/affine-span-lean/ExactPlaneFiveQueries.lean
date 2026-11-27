import ExactPlaneCandidateCheck
namespace ExactPlaneFiveQueries
open ExactPlanePhysicalConverse
abbrev P := F × F
variable {I K : Type*} [DecidableEq I] [AddCommGroup K] [Module F K]
abbrev V (K : Type*) := K × P × P
def one : P := (1,0)
def two : P := (0,1)
def three : P := (1,1)

theorem five_iff (A : Finset I) (k : I → K) (b h : I → P) :
    let S := physicalSpan k b h A
    ExactTrace k b h A ↔
      ((0:K),(0:P),one) ∈ S ∧ ((0:K),(0:P),two) ∈ S ∧
      ((0:K),one,(0:P)) ∉ S ∧ ((0:K),two,(0:P)) ∉ S ∧ ((0:K),three,(0:P)) ∉ S := by
  intro S
  constructor
  · intro ok
    exact ⟨(ok 0 one).mpr rfl,(ok 0 two).mpr rfl,fun hz => (by decide : one ≠ 0) ((ok one 0).mp hz),
      fun hz => (by decide : two ≠ 0) ((ok two 0).mp hz),
      fun hz => (by decide : three ≠ 0) ((ok three 0).mp hz)⟩
  · rintro ⟨p,q,a,b',c⟩
    have axes (v : P) : ((0:K),(0:P),v) ∈ S := by
      have m := S.add_mem (S.smul_mem v.1 p) (S.smul_mem v.2 q)
      simpa [one,two,Prod.smul_mk,Prod.mk_add_mk,smul_eq_mul] using m
    intro z y
    constructor
    · intro hv
      have hz : ((0:K),z,(0:P)) ∈ S := by simpa using S.sub_mem hv (axes y)
      have cases4 : ∀ z : P,z=0 ∨ z=one ∨ z=two ∨ z=three := by decide
      rcases cases4 z with e|e|e|e
      · exact e
      · subst z; exact (a hz).elim
      · subst z; exact (b' hz).elim
      · subst z; exact (c hz).elim
    · rintro rfl; exact axes y

def findSupports (solve : V K → Option (Finset I)) : Option (Finset I × Finset I) := do
  let u ← solve (0,0,one)
  let v ← solve (0,0,two)
  if (solve (0,one,0)).isNone && (solve (0,two,0)).isNone && (solve (0,three,0)).isNone
    then some (u,v) else none

theorem findSupports_spec [DecidableEq K] (A : Finset I) (k : I → K) (b h : I → P)
    (solve : V K → Option (Finset I))
    (correct : ∀ v,(solve v).isSome = true ↔ v ∈ physicalSpan k b h A)
    (sound : ∀ v U,solve v=some U → U⊆A ∧ ExactPlaneCandidateCheck.total k b h U=v) :
    ((findSupports solve).isSome=true ↔ ExactTrace k b h A) ∧
    ∀ u v,findSupports solve=some (u,v) →
      (u⊆A ∧ ExactPlaneCandidateCheck.total k b h u=(0,0,one)) ∧
      (v⊆A ∧ ExactPlaneCandidateCheck.total k b h v=(0,0,two)) := by
  have eq := five_iff A k b h
  dsimp only at eq
  rw [eq]
  simp only [← correct]
  cases e₁ : solve (0,0,one) <;> cases e₂ : solve (0,0,two) <;>
    cases e₃ : solve (0,one,0) <;> cases e₄ : solve (0,two,0) <;>
    cases e₅ : solve (0,three,0) <;> simp [findSupports,e₁,e₂,e₃,e₄,e₅]
  all_goals exact ⟨sound _ _ e₁,sound _ _ e₂⟩

#print axioms five_iff
#print axioms findSupports_spec
end ExactPlaneFiveQueries
