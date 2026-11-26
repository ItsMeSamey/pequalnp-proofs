import T2PhysicalOverride

namespace T2RawTopology
open ResidualSurplus T2PhysicalOverride

def RawValid : Nat → List Raw → Prop
  | _, [] => True
  | n, r::rs => r.2.1 < n ∧ r.2.2 < n ∧ RawValid (n+1) rs

theorem annotate_valid_iff (n : Nat) (gs : List Raw) (ts : List Tag) :
    Valid n (annotate gs ts) ↔ RawValid n gs := by
  induction gs generalizing n ts with
  | nil => rfl
  | cons r rs ih =>
    obtain ⟨o,x,y⟩ := r
    simp [annotate,Valid,RawValid,ih]

theorem shift_valid (gs : List Raw) (n : Nat) (h : RawValid n gs) :
    RawValid (n+1) (gs.map rawShift) := by
  induction gs generalizing n with
  | nil => trivial
  | cons r rs ih =>
    obtain ⟨o,x,y⟩ := r
    obtain ⟨hx,hy,tail⟩ := h
    exact ⟨Nat.succ_lt_succ hx,Nat.succ_lt_succ hy,ih _ tail⟩

theorem rawEdited_valid (pre post : List Raw) (r : Raw) (n : Nat)
    (h : RawValid n (pre ++ r::post)) : RawValid (n+1) (rawEdited pre post r.1) := by
  induction pre generalizing n with
  | nil => exact ⟨Nat.zero_lt_succ _, Nat.zero_lt_succ _, shift_valid post _ h.2.2⟩
  | cons s ss ih =>
    obtain ⟨o,x,y⟩ := s
    obtain ⟨hx,hy,tail⟩ := h
    exact ⟨Nat.succ_lt_succ hx,Nat.succ_lt_succ hy, ih _ tail⟩

#print axioms rawEdited_valid
end T2RawTopology
