import Mathlib.Data.Set.Prod

namespace IncidenceRightDerivative

inductive Expr (P L : Type*) where
  | point : P → Expr P L
  | line : L → Expr P L
  | join : Expr P L → Expr P L → Expr P L
  | meet : Expr P L → Expr P L → Expr P L

variable {P L : Type*}

def eval (x : Set P) (y : Set L) : Expr P L → Prop
  | .point p => p ∈ x
  | .line l => l ∈ y
  | .join a b => eval x y a ∨ eval x y b
  | .meet a b => eval x y a ∧ eval x y b

/-- A true parse using exactly k occurrences of line-input leaves. -/
def cert (x : Set P) (y : Set L) : Expr P L → ℕ → Prop
  | .point p,k => k=0 ∧ p∈x
  | .line l,k => k=1 ∧ l∈y
  | .join a b,k => cert x y a k ∨ cert x y b k
  | .meet a b,k => ∃ i j, i+j=k ∧ cert x y a i ∧ cert x y b j

theorem cert_true (x : Set P) (y : Set L) (e : Expr P L) :
    (∃ k, cert x y e k) ↔ eval x y e := by
  induction e with
  | point p => simp [eval,cert]
  | line l => simp [eval,cert]
  | join a b ha hb =>
    change (∃ k, cert x y a k ∨ cert x y b k) ↔ _
    simp [exists_or, ha,hb,eval]
  | meet a b ha hb =>
    constructor
    · rintro ⟨_,i,j,_,hi,hj⟩
      exact ⟨ha.mp ⟨i,hi⟩,hb.mp ⟨j,hj⟩⟩
    · rintro ⟨at',bt⟩
      obtain ⟨i,hi⟩ := ha.mpr at'
      obtain ⟨j,hj⟩ := hb.mpr bt
      exact ⟨i+j,i,j,rfl,hi,hj⟩

theorem cert_zero (x : Set P) (y : Set L) (e : Expr P L) :
    cert x y e 0 ↔ eval x ∅ e := by
  induction e with
  | point p => simp [eval,cert]
  | line l => simp [eval,cert]
  | join a b ha hb => simp [eval,cert,ha,hb]
  | meet a b ha hb => simp [eval,cert,ha,hb]

theorem cert_one_meet (x : Set P) (y : Set L) (a b : Expr P L) :
    cert x y (.meet a b) 1 ↔
      (cert x y a 1 ∧ eval x ∅ b) ∨ (eval x ∅ a ∧ cert x y b 1) := by
  constructor
  · rintro ⟨i,j,ij,hi,hj⟩
    have h : (i=1 ∧ j=0) ∨ (i=0 ∧ j=1) := by omega
    rcases h with ⟨rfl,rfl⟩|⟨rfl,rfl⟩
    · exact Or.inl ⟨hi,(cert_zero _ _ _).mp hj⟩
    · exact Or.inr ⟨(cert_zero _ _ _).mp hi,hj⟩
  · rintro (⟨a1,b0⟩|⟨a0,b1⟩)
    · exact ⟨1,0,rfl,a1,(cert_zero _ _ _).mpr b0⟩
    · exact ⟨0,1,rfl,(cert_zero _ _ _).mpr a0,b1⟩

def shield (e : Expr P L) (p₀ p₁ : P) (l₀ : L) : Expr P L :=
  .meet (.join e (.meet (.point p₀) (.point p₁)))
    (.join e (.line l₀))

theorem shield_eval (e : Expr P L) (p₀ p₁ : P) (l₀ : L)
    (edge : ∀ (x : Set P) (y : Set L), p₀∈x → l₀∈y → eval x y e) (x : Set P) (y : Set L) :
    eval x y (shield e p₀ p₁ l₀) ↔ eval x y e := by
  change ((eval x y e ∨ _) ∧ (eval x y e ∨ _)) ↔ eval x y e
  constructor
  · rintro ⟨h|a,g|b⟩
    · exact h
    · exact h
    · exact g
    · exact edge _ _ a.1 b
  · exact fun h => ⟨Or.inl h,Or.inl h⟩

theorem shield_has_no_one_right_parse (e : Expr P L) (p₀ p₁ : P) (l₀ : L)
    (off : ∀ x : Set P, ¬eval x ∅ e) (different : p₀ ≠ p₁) (p : P) (y : Set L) :
    ¬cert {p} y (shield e p₀ p₁ l₀) 1 := by
  intro h
  rw [shield,cert_one_meet] at h
  have never : ¬(p₀=p ∧ p₁=p) := fun h => different (h.1.trans h.2.symm)
  simp [eval,off,never] at h

end IncidenceRightDerivative
