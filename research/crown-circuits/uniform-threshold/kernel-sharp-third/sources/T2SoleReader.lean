
namespace T2RawReader

/-- A sole reader of an input is the only way the input can affect the result. -/
theorem sole_or_clean (P : Bool) (context : Bool → Bool)
    (single : context (false || P) = false) (pair : context (true || P) = true) :
    P = false := by
  cases P <;> simp_all

theorem sole_and_dirty (P : Bool) (context : Bool → Bool)
    (single : context (false && P) = false) (pair : context (true && P) = true) :
    P = true := by
  cases P <;> simp_all

end T2RawReader

namespace T2RawReader

/-- Reconnect a sole OR reader directly to its raw input and move its other
operand to an output OR. This uses the global implicant condition on inputs. -/
theorem move_sole_or {A : Type} (x P : A → Bool) (context : A → Bool → Bool)
    (implicant : ∀ a, P a = true → context a (x a || P a) = true) (a : A) :
    (context a (x a) || P a) = context a (x a || P a) := by
  cases h : P a with
  | false => simp [h]
  | true => simpa [h] using (implicant a h).symm

end T2RawReader

namespace T2RawReader

/-- Set a maximum signal to one after pinning the sole AND-reader raw to zero.
At nonzero assignments the replacement already agrees. At zero the specialized
network is bounded above by its (rejecting) value at a singleton. -/
theorem force_maximum {A : Type} (zero singleton : A) (P : A → Bool)
    (downstream : A → Bool → Bool)
    (nonzero : ∀ a, a ≠ zero → P a = true)
    (singleton_nonzero : singleton ≠ zero)
    (zero_reject : downstream zero (P zero) = false)
    (singleton_reject : downstream singleton (P singleton) = false)
    (monotone_step : downstream zero true = true → downstream singleton true = true)
    (a : A) : downstream a true = downstream a (P a) := by
  by_cases hz : a = zero
  · subst a
    rw [zero_reject]
    cases h : downstream zero true with
    | false => rfl
    | true =>
      have hs := monotone_step h
      rw [nonzero singleton singleton_nonzero] at singleton_reject
      simp_all
  · rw [nonzero a hz]

end T2RawReader
