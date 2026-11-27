import ExactPlaneRawSectionCheck
namespace ExactPlaneSectionCheckComplete
open ExactPlaneSparseANF ExactPlaneSparseSections ExactPlaneSparseValidation ExactPlaneRawSectionCheck
open ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial ExactPlaneSuppliedCoordinates
open ExactPlaneAffineSpanHit ExactPlaneProfileCharts
open scoped BigOperators
variable {I : Type*} [DecidableEq I] {r N d : ℕ}

theorem ext_eval {f g : Form I} (eq : ∀ A,eval (coeff f) A=eval (coeff g) A) : f=g := by
  let c : Coeff I := fun U=>coeff f U-coeff g U
  have z (A : Finset I) : eval c A=0 := by
    change (∑ U∈A.powerset,(coeff f U-coeff g U))=0
    rw [Finset.sum_sub_distrib]
    exact sub_eq_zero.mpr (eq A)
  ext U
  have cz := ((low_coeff_zero_iff_low_eval_zero c U.card).mpr
    (fun A _=>z A)) U le_rfl
  have he := sub_eq_zero.mp cz
  by_cases hf : U∈f <;> by_cases hg : U∈g <;> simp_all [coeff]

def bits (A : Finset I) : I→F := fun i=>if i∈A then 1 else 0
theorem support_bits [Fintype I] (A : Finset I) : support (bits A)=A := by
  ext i; simp [bits,support]

theorem valid_of_phys (p : Fin N→Key d) (tag : Fin N→F×F) (f : Weights d N r)
    (u : Fin r→Key d) (ind : LinearIndependent F u)
    (phys : ∀ (x : X d) j, chosen (f j) (support x)⊆active p tag x ∧
      (∑ i∈chosen (f j) (support x),p i)=u j) : valid p tag f=true := by
  have supportAt (A : Finset (Fin (d+d))) (j) :=
    (show chosen (f j) A ⊆ active p tag (bits A) ∧ (∑ i∈chosen (f j) A,p i)=u j from
      by simpa only [support_bits] using phys (bits A) j)
  have valkey (j : Fin r) (c : Fin d) (A : Finset (Fin (d+d))) :
      eval (coeff (lc (f j) (fun i=>p i c))) A=u j c := by
    rw [←chosen_sum]
    simpa only [Finset.sum_apply] using congrFun (supportAt A j).2 c
  have sameU : direction p f=u := by
    funext j c
    simpa [direction,eval] using valkey j c ∅
  have tagzero (j : Fin r) (i : Fin N) (side : Bool) : times (f j i) (bad p tag i side)=∅ := by
    apply ext_eval
    intro A
    rw [eval_empty]
    have ident : coeff (times (f j i) (bad p tag i side)) =
        product (coeff (f j i)) (coeff (bad p tag i side)) := funext (fun U=>coeff_times _ _ U)
    rw [ident,product_eval]
    have bit : ∀ z:F,z=0 ∨ z=1 := by decide
    rcases bit (eval (coeff (f j i)) A) with cold|hot
    · rw [cold,zero_mul]
    · have mem := (supportAt A j).1 (Finset.mem_filter.mpr ⟨Finset.mem_univ _,hot⟩)
      have match' := (mem_active p tag (bits A) i).mp mem
      rw [←table_chart] at match'
      have h := eval_bad p tag (bits A) i side
      rw [support_bits,match',CharTwo.add_self_eq_zero (component (tag i) side)] at h
      rw [hot,h,mul_zero]
  have constKey (j : Fin r) (c : Fin d) : lc (f j) (fun i=>p i c)=constant (u j c) := by
    apply ext_eval
    intro A
    rw [eval_constant,valkey]
  have rank : ExactPlaneComputedDeficit.keyRank u Finset.univ=r := by
    rw [ExactPlaneComputedDeficit.keyRank_eq]
    have eq : Set.range (fun i : ↥(Finset.univ : Finset (Fin r)) => u i.val)=Set.range u := by
      ext z; constructor
      · rintro ⟨i,rfl⟩; exact ⟨i.val,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨⟨i,Finset.mem_univ _⟩,rfl⟩
    rw [eq,finrank_span_eq_card ind,Fintype.card_fin]
  simp [valid,check,sameU,tagzero,constKey,rank]

theorem valid_iff_phys (p : Fin N→Key d) (tag : Fin N→F×F) (f : Weights d N r) :
    valid p tag f=true ↔ ∃ u : Fin r→Key d, LinearIndependent F u ∧
      ∀ (x : X d) j, chosen (f j) (support x) ⊆ active p tag x ∧
        (∑ i∈chosen (f j) (support x),p i)=u j :=
  ⟨fun h=>⟨_,(valid_sound h)⟩,fun ⟨u,hi,h⟩=>valid_of_phys p tag f u hi h⟩
#print axioms valid_iff_phys
end ExactPlaneSectionCheckComplete
