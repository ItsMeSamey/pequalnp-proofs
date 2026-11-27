import ExactPlaneSparseValidation
import ExactPlaneProfileCharts
import ExactPlaneComputedDeficit
import Mathlib.LinearAlgebra.Dimension.OrzechProperty
namespace ExactPlaneRawSectionCheck
open ExactPlaneSparseANF ExactPlaneSparseSections ExactPlaneSparseValidation
open ExactPlaneAffineSubstitution ExactPlaneSubsetPolynomial ExactPlaneSuppliedCoordinates
open ExactPlaneProfileCharts ExactPlaneAffineSpanHit
open scoped BigOperators
variable {d N r : ℕ}
abbrev Weights (d N r : ℕ) := Fin r→Fin N→Form (Fin (d+d))

def variableAt (j : Fin (d+d)) : Form (Fin (d+d)) := {{j}}
def index (d : ℕ) (b : Bool) (i : Fin d) : Fin (d+d) :=
  if b then Fin.natAdd d i else Fin.castAdd d i
def component (z : F×F) (b : Bool) : F := if b then z.2 else z.1

def bad (p : Fin N→Key d) (tag : Fin N→F×F) (i : Fin N) (side : Bool) :=
  plus (constant (component (tag i) side))
    (lc (fun j=>variableAt (index d side j)) (p i))

theorem eval_plus (a b : Form (Fin (d+d))) (A : Finset (Fin (d+d))) :
    eval (coeff (plus a b)) A=eval (coeff a) A+eval (coeff b) A := by
  simp only [eval,coeff_plus,Finset.sum_add_distrib]

theorem var_eval (x : X d) (v : Fin (d+d)) :
    eval (coeff (variableAt v)) (support x)=x v := by
  have bit : ∀ z:F,z=0 ∨ z=1 := by decide
  rcases bit (x v) with h|h <;> simp [eval,coeff,variableAt,support,h]

theorem eval_bad (p : Fin N→Key d) (tag : Fin N→F×F) (x : X d) (i : Fin N) (side : Bool) :
    eval (coeff (bad p tag i side)) (support x) =
    component (tag i) side + component (table p x i) side := by
  rw [bad,eval_plus,eval_constant,eval_height]
  cases side <;> simp [var_eval,component,index,table,value,ExactPlaneGeneratedDecision.coordinate,
    Prod.fst_sum,Prod.snd_sum]

def direction (p : Fin N→Key d) (f : Weights d N r) (j : Fin r) : Key d :=
  fun c => coeff (lc (f j) (fun i=>p i c)) ∅

def valid (p : Fin N→Key d) (tag : Fin N→F×F) (f : Weights d N r) :=
  check f (bad p tag) p (direction p f) &&
    decide (ExactPlaneComputedDeficit.keyRank (direction p f) Finset.univ=r)

theorem valid_sound {p : Fin N→Key d} {tag : Fin N→F×F} {f : Weights d N r}
    (ok : valid p tag f=true) :
    LinearIndependent F (direction p f) ∧
    ∀ (x : X d) j, chosen (f j) (support x) ⊆ active p tag x ∧
      (∑ i∈chosen (f j) (support x),p i)=direction p f j := by
  obtain ⟨checks,rank⟩ := (show check f (bad p tag) p (direction p f)=true ∧
      ExactPlaneComputedDeficit.keyRank (direction p f) Finset.univ=r from by simpa [valid] using ok)
  refine ⟨?_,?_⟩
  · rw [ExactPlaneComputedDeficit.keyRank_eq] at rank
    have eq : Set.range (fun i : ↥(Finset.univ : Finset (Fin r)) => direction p f i.val)
        = Set.range (direction p f) := by
      ext z; constructor
      · rintro ⟨i,rfl⟩; exact ⟨i.val,rfl⟩
      · rintro ⟨i,rfl⟩; exact ⟨⟨i,Finset.mem_univ _⟩,rfl⟩
    rw [eq] at rank
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    rw [Fintype.card_fin]
    exact rank.symm
  · intro x j
    obtain ⟨act,key⟩ := sound checks j (support x)
    refine ⟨?_,key⟩
    intro i hi
    have a := act i hi false
    have b := act i hi true
    rw [eval_bad] at a b
    apply (mem_active p tag x i).mpr
    rw [←table_chart]
    apply Prod.ext
    · exact (CharTwo.add_eq_zero.mp a).symm
    · exact (CharTwo.add_eq_zero.mp b).symm

#print axioms valid_sound
end ExactPlaneRawSectionCheck
