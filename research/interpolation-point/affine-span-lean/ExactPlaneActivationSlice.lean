import ExactPlaneAffineSpanHit
namespace ExactPlaneActivationSlice
open ExactPlaneAffineSpanHit ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution
variable {J K : Type*} [Fintype J] [DecidableEq J]
def Active (read : K→Vec J →ₗ[ZMod 2] ZMod 2) (offset target : K→ZMod 2) (x : Vec J) : Prop :=
  ∀ k,read k x+offset k=target k

theorem span_active (read : K→Vec J →ₗ[ZMod 2] ZMod 2) (offset target : K→ZMod 2)
    (S : Finset (Vec J)) (valid : ∀ x∈S,Active read offset target x)
    {x : Vec J} (hx : x∈affineSpan (ZMod 2) (S:Set (Vec J))) : Active read offset target x := by
  refine affineSpan_induction (p:=Active read offset target) hx valid ?_
  intro c u v w hu hv hw k
  change read k (c • (u-v)+w)+offset k=target k
  have eq : read k u=read k v := add_right_cancel ((hu k).trans (hv k).symm)
  simp only [map_add,map_smul,map_sub,eq,sub_self,smul_zero,zero_add]
  exact hw k

theorem odd_sum_active (read : K→Vec J →ₗ[ZMod 2] ZMod 2) (offset target : K→ZMod 2)
    (l : List (Vec J)) (valid : ∀ x∈l,Active read offset target x)
    (odd : l.length%2=1) : Active read offset target l.sum := by
  intro k
  have parity (xs : List (Vec J)) (ok : ∀ x∈xs,Active read offset target x) :
      read k xs.sum=(if xs.length%2=0 then 0 else target k-offset k) := by
    induction xs with
    | nil => simp
    | cons x xs ih =>
      have hx : read k x=target k-offset k := eq_sub_of_add_eq ((ok x (by simp)) k)
      have tail := ih (fun z hz => ok z (by simp [hz]))
      by_cases e : xs.length%2=0
      · have ne : (xs.length+1)%2≠0 := by omega
        simp [List.length_cons,e,ne,hx,tail]
      · have ne : (xs.length+1)%2=0 := by omega
        simp [List.length_cons,e,ne,hx,tail,CharTwo.add_self_eq_zero]
  rw [parity l valid,if_neg (by omega)]
  exact sub_add_cancel _ _

noncomputable def slice (seed : Finset (Vec J)) (read : K→Vec J →ₗ[ZMod 2] ZMod 2)
    (offset target : K→ZMod 2) : Finset (Vec J) := by
  classical exact seed.filter (Active read offset target)

theorem quartic_active (seed : Finset (Vec J)) (read : K→Vec J →ₗ[ZMod 2] ZMod 2)
    (offset target : K→ZMod 2) (c : Coeff J) (degree : degreeLE 4 c)
    (hit : ∃ x∈affineSpan (ZMod 2) (slice seed read offset target:Set (Vec J)),eval c (support x)≠0) :
    ∃ l : List (Vec J),(∀ x∈l,x∈seed ∧ Active read offset target x) ∧
      (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
      l.sum∈affineSpan (ZMod 2) (slice seed read offset target:Set (Vec J)) ∧
      Active read offset target l.sum ∧ eval c (support l.sum)≠0 := by
  classical
  obtain ⟨l,hl,len,sp,hot⟩ := quartic_span_hit _ c degree hit
  exact ⟨l,fun x hx => Finset.mem_filter.mp (hl x hx),len,sp,
    span_active read offset target _ (fun x hx => (Finset.mem_filter.mp hx).2) sp,hot⟩

theorem localize {score : Vec J→Prop} (seed : Finset (Vec J))
    (read : K→Vec J →ₗ[ZMod 2] ZMod 2) (offset target : K→ZMod 2) (domain : Set (Vec J))
    (coverage : ∀ x∈domain,Active read offset target x →
      x∈affineSpan (ZMod 2) (slice seed read offset target:Set (Vec J)))
    (witness : ∃ x∈domain,Active read offset target x ∧ score x) :
    ∃ x∈affineSpan (ZMod 2) (slice seed read offset target:Set (Vec J)),score x := by
  obtain ⟨x,hx,active,hot⟩ := witness
  exact ⟨x,coverage x hx active,hot⟩
#print axioms span_active
#print axioms odd_sum_active
#print axioms quartic_active
end ExactPlaneActivationSlice
