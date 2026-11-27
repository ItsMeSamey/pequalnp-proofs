import ExactPlaneWedgeArrayDP
namespace ExactPlaneWedgeTreeCharges
open ExactPlaneWedgeArrayDP
variable {n m : Nat}

def tips : {m : Nat} → Plan n m → Nat
  | _,.leaf _ _ => 1
  | _,.join l r _ _ => tips l + tips r

def joins : {m : Nat} → Plan n m → Nat
  | _,.leaf _ _ => 0
  | _,.join l r _ _ => joins l + joins r + 1

def checks : {m : Nat} → Plan n m → Nat
  | _,.leaf _ _ => 0
  | _,@Plan.join _ a b l r c _ => checks l + checks r + c*(a*b)

def Fits (q : Nat) : {m : Nat} → Plan n m → Prop
  | _,.leaf m _ => m≤q
  | _,.join l r m _ => Fits q l ∧ Fits q r ∧ m≤q

theorem balance (p : Plan n m) : joins p + 1 = tips p := by
  induction p with
  | leaf => rfl
  | join l r m ok hl hr => simp only [joins,tips]; omega

theorem size_fit {q : Nat} (p : Plan n m) (fit : Fits q p) : m≤q := by
  cases p with
  | leaf => exact fit
  | join => exact fit.2.2

theorem checks_cap (q : Nat) (p : Plan n m) (fit : Fits q p) :
    checks p ≤ joins p*(q*(q*q)) := by
  induction p with
  | leaf => simp [checks,joins]
  | join l r m ok hl hr =>
    obtain ⟨fl,fr,fm⟩ := fit
    have last := Nat.mul_le_mul fm (Nat.mul_le_mul (size_fit l fl) (size_fit r fr))
    simp only [checks,joins,Nat.add_mul,one_mul]
    exact Nat.add_le_add (Nat.add_le_add (hl fl) (hr fr)) last
#print axioms checks_cap
end ExactPlaneWedgeTreeCharges
