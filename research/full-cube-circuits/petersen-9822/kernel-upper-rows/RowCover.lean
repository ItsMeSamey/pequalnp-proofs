import FourSaturationData
namespace Research.Graph9822.FourSaturation
set_option maxRecDepth 100000
set_option maxHeartbeats 0

def edgeMask (e : Nat × Nat) : Nat := (1 <<< e.1) ||| (1 <<< e.2)
def below (a b : Nat) : Bool := (a &&& b) == a
def covered (m : Nat) : Bool :=
  if accepts m then edges.any (fun e => below (edgeMask e) m)
  else witnesses.any (fun w => below m w)

theorem every_mask_covered (m : Fin 1024) : covered m.val = true := by
  have h : ∀ i : Fin 1024, covered i.val = true := by decide +kernel
  exact h m

theorem checked_rows_suffice (f : Nat → Bool)
    (mono : ∀ a b, below a b = true → f a = true → f b = true)
    (positive : ∀ e ∈ edges, f (edgeMask e) = true)
    (negative : ∀ w ∈ witnesses, f w = false)
    (m : Fin 1024) : f m.val = accepts m.val := by
  have cov := every_mask_covered m
  cases hm : accepts m.val with
  | false =>
    have hn : witnesses.any (fun w => below m.val w) = true := by
      simpa [covered, hm] using cov
    obtain ⟨w, hw, he⟩ := List.any_eq_true.mp hn
    cases hf : f m.val with
    | false => rfl
    | true =>
      have hbad := mono m.val w he hf
      rw [negative w hw] at hbad
      contradiction
  | true =>
    have hp : edges.any (fun e => below (edgeMask e) m.val) = true := by
      simpa [covered, hm] using cov
    obtain ⟨e, he, hsub⟩ := List.any_eq_true.mp hp
    exact mono (edgeMask e) m.val hsub (positive e he)
end Research.Graph9822.FourSaturation
