import BinatePins
import LiveUses

namespace SignedTrace
open PEqualNP.CircuitLowerBounds ActualUses Physical Gates

/-- Terminal wire of a walk through unique output-live consuming pins. -/
def stopWire {out : Nat → List Use} {w : Nat} : ForkWalk.Walk out w → Nat
  | .unused _ | .output _ _ | .fork _ _ _ _ => w
  | .step _ _ _ tail => stopWire tail

private theorem same_sign_at_empty {C : Circuit} {n w : Nat} {s e o : Bool}
    {xs ys : List FirstDivergence.Hop}
    (he : FirstDivergence.Run C n w s C.output e xs)
    (ho : FirstDivergence.Run C n w s C.output o ys)
    (hp : ∀ a : Nat × Nat, Use.pin a.1 a.2 ∉ LiveUses.outgoing C n w) : e = o := by
  cases xs with
  | cons x xs => exact False.elim ((hp x) (LiveUses.run_along he).1)
  | nil =>
    cases ys with
    | cons y ys => exact False.elim ((hp y) (LiveUses.run_along ho).1)
    | nil => exact he.2.symm.trans ho.2

private theorem fork_on_two_runs {C : Circuit} {n w : Nat}
    (walk : ForkWalk.Walk (LiveUses.outgoing C n) w) :
    ∀ {s e o : Bool} {xs ys : List FirstDivergence.Hop},
    FirstDivergence.Run C n w s C.output e xs →
    FirstDivergence.Run C n w s C.output o ys → e ≠ o →
    2 ≤ (LiveUses.outgoing C n (stopWire walk)).length := by
  induction walk with
  | unused h =>
    intro s e o xs ys he ho hne
    exact (hne (same_sign_at_empty he ho (by simp [h]))).elim
  | output t h =>
    intro s e o xs ys he ho hne
    exact (hne (same_sign_at_empty he ho (by simp [h]))).elim
  | fork a b rest h => simp [stopWire, h]
  | @step w v p h rest ih =>
    intro s e o xs ys he ho hne
    have hp : Use.pin v p ∈ LiveUses.outgoing C n w := by simp [h]
    have hb := LiveUses.pin_iff.mp hp
    have hlt := hb.1.2.1
    have hle := LiveUses.bounded hb.2
    cases xs with
    | nil => have hw := he.1; omega
    | cons a xs =>
      cases ys with
      | nil => have hw := ho.1; omega
      | cons b ys =>
        have ha := (LiveUses.run_along he).1
        have hb' := (LiveUses.run_along ho).1
        have ea : a = (v,p) := by
          rcases a with ⟨u,j⟩
          simp [h] at ha
          exact Prod.ext ha.1 ha.2
        have eb : b = (v,p) := by
          rcases b with ⟨u,j⟩
          simp [h] at hb'
          exact Prod.ext hb'.1 hb'.2
        subst a
        subst b
        exact ih he.2 ho.2 hne

/-- The first producer with two DIFFERENT live pin uses must exist for a
physically binate donor. The count counts occurrences, including equal-source
pins on one gate; both assignment pairs may have different backgrounds. -/
theorem binate_firstFork (C : Circuit) (n d : Nat)
    (good : ∀ g ∈ C.gates, Good g) (binate : BinateDonor C n d) :
    2 ≤ (LiveUses.outgoing C n (stopWire (LiveUses.firstFork C n d))).length := by
  obtain ⟨⟨_, _, xs, _, _, _, hx⟩, ⟨_, _, ys, _, _, _, hy⟩⟩ :=
    binate_with_pins C n d good binate
  exact fork_on_two_runs (LiveUses.firstFork C n d)
    (FirstDivergence.certificate_walk hx) (FirstDivergence.certificate_walk hy) (by decide)

end SignedTrace
