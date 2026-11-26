import ThresholdStarShieldPhysical
import ThresholdStarPromotion
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction T2SoleOrSplice

/-- Direct wire form: if x is blocked, only its selected group root can change.
Thus a second blocked partner has to be that precise root, whose bypassed
value is false on a third singleton. -/
theorem physical_dead_unique {n : Nat} (star : Finset (Fin n)) (priv : Finset (Fin n))
    (small : priv⊆star) (third : ∀ x∈priv,∀ y∈priv,x≠y → ∃ z∈star,z≠x ∧ z≠y)
    (snap : Finset (Fin n) → Env) (wire opposite : Fin n → Nat)
    (sole : ∀ x∈priv,snap ∅ (opposite x)=false → Away (wire x) (snap ∅) (snap {x}))
    (admits : ∀ x∈priv,∀ z∈star,z≠x → snap {z} (opposite x)=true)
    (aliases : ∀ x∈priv,∀ z∈star,z≠x → snap {z} (wire x)=false)
    (x y : Fin n) (hx : x∈priv) (hy : y∈priv)
    (dx : snap ∅ (opposite x)=false) (dy : snap ∅ (opposite y)=false) : x=y := by
  by_contra xy
  have yx := admits y hy x (small hx) xy
  have must : opposite y=wire x := by
    by_contra ne
    have same := sole x hx dx (opposite y) ne
    rw [dy,yx] at same
    contradiction
  obtain ⟨z,hz,zx,zy⟩ := third x hx y hy xy
  have yz := admits y hy z hz zy
  rw [must,aliases x hx z hz zx] at yz
  contradiction

/-- A shielded singleton cannot be the rejecting side of a threshold
singleton/pair comparison. Every terminal tap is covered by the shield. -/
theorem partner_admits {n : Nat} (bs : List Block) (u v out : Nat) (sel : Nat → Bool)
    (x y : Fin n) (xy : x≠y) (opp : Nat) (f : Env)
    (shield : run u sel true (fun j => (vector {y}).getD j false) bs f opp=false →
      Shielded u x.val v sel (fun j => (vector {y}).getD j false) bs f)
    (outside : ∀ b∈bs, OutsideTaps u v sel b) (notOut : out≠v)
    (sem : ∀ s : Finset (Fin n), s={y} ∨ s=insert x {y} →
      ((run u sel true (fun j => (vector s).getD j false) bs f out ||
        taps u sel (fun j => (vector s).getD j false) bs f)=true ↔ 2≤s.card)) :
    run u sel true (fun j => (vector {y}).getD j false) bs f opp=true := by
  cases h : run u sel true (fun j => (vector {y}).getD j false) bs f opp with
  | true => rfl
  | false =>
    have same := shielded_promoted u x.val v sel _ _ (off_insert {y} x).2 bs f f
      (fun _ _ => rfl) (shield h) outside out notOut
    have yes := (sem (insert x {y}) (Or.inr rfl)).mpr (by simp [xy])
    have no := (sem {y} (Or.inl rfl)).mp (same.trans yes)
    simp at no
#print axioms physical_dead_unique
#print axioms partner_admits
end ThresholdStarBypass
