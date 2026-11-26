import Mathlib.FieldTheory.Finite.GaloisField
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Data.Nat.Find
namespace ExactPlaneFieldCard

theorem dual_card (V : Type*) [AddCommGroup V] [Module (ZMod 2) V] [Fintype V]
    [FiniteDimensional (ZMod 2) V] [Fintype (V →ₗ[ZMod 2] ZMod 2)] :
    Fintype.card (V →ₗ[ZMod 2] ZMod 2)=Fintype.card V :=
  Fintype.card_congr (Module.finBasis (ZMod 2) V).toDualEquiv.toEquiv.symm

private theorem exists_exp (t : Nat) : ∃ e : Nat,t<2^e := ⟨t,t.lt_two_pow_self⟩
noncomputable def exponent (t : Nat) := Nat.find (exists_exp t)

theorem least (t j : Nat) (hit : t<2^j) : exponent t ≤ j := Nat.find_min' _ hit

theorem band (t : Nat) (ht : 0<t) :
    0<exponent t ∧ t<2^(exponent t) ∧ 2^(exponent t)≤2*t := by
  have strict : t<2^(exponent t) := Nat.find_spec (exists_exp t)
  cases h : exponent t with
  | zero => simp [h] at strict; omega
  | succ e =>
    have prior : ¬t<2^e := fun he => by have le := least t e he; omega
    have weak : 2^e≤t := Nat.le_of_not_gt prior
    rw [h] at strict
    exact ⟨Nat.zero_lt_succ _,strict,by simpa [pow_succ,Nat.mul_comm] using Nat.mul_le_mul_left 2 weak⟩

abbrev K (t : Nat) := GaloisField 2 (exponent t)

theorem field_card (t : Nat) (ht : 0<t) [Fintype (K t)] :
    Fintype.card (K t)=2^(exponent t) := by
  rw [←Nat.card_eq_fintype_card]
  exact GaloisField.card 2 (exponent t) (Nat.ne_of_gt (band t ht).1)

theorem seed_bound (m R : Nat) (hm : 0<m) [Fintype (K (m*2^R))]
    [Fintype (K (m*2^R) →ₗ[ZMod 2] ZMod 2)] :
    m*2^R < Fintype.card (K (m*2^R)) ∧
    Fintype.card (K (m*2^R))*Fintype.card (K (m*2^R) →ₗ[ZMod 2] ZMod 2) ≤
      (2*m*2^R)^2 := by
  have hp : 0<m*2^R := Nat.mul_pos hm (by positivity)
  rw [dual_card,field_card _ hp]
  obtain ⟨_,strict,upper⟩ := band _ hp
  exact ⟨strict,by simpa [pow_two,Nat.mul_assoc] using Nat.mul_le_mul upper upper⟩

#print axioms dual_card
#print axioms seed_bound
end ExactPlaneFieldCard
