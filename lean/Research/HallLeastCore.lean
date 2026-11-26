import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.EquivFin

namespace HallLeastCore

variable {C V : Type*} [Finite V]

/-- owner is the inverse matching, with none denoting a free variable. -/
inductive Reach (edge : C → V → Prop) (owner : V → Option C) : C → Prop where
  | free (c) (h : ∀ v, owner v ≠ some c) : Reach edge owner c
  | step {c v d} (hc : Reach edge owner c) (hv : edge c v)
      (hd : owner v = some d) : Reach edge owner d

def Core (edge : C → V → Prop) (owner : V → Option C) (v : V) : Prop :=
  ∃ c, Reach edge owner c ∧ edge c v

def External (edge : C → V → Prop) (B : V → Prop) (c : C) : Prop :=
  ∃ v, edge c v ∧ ¬ B v

def Feasible (edge : C → V → Prop) (B : V → Prop) : Prop :=
  ∃ f : {c // External edge B c} → V, Function.Injective f ∧
    ∀ c, edge c.val (f c) ∧ ¬ B (f c)

/-- The local stopping condition is that each reached variable has an owner.
This is the no-augmenting-path condition at the end of the matching algorithm. -/
theorem subset_of_feasible (edge : C → V → Prop) (owner : V → Option C)
    (matchedEdge : ∀ {v c}, owner v = some c → edge c v)
    (uniqueVar : ∀ {v w c}, owner v = some c → owner w = some c → v = w)
    (closed : ∀ v, Core edge owner v → ∃ c, owner v = some c)
    (B : V → Prop) (feas : Feasible edge B) :
    ∀ v, Core edge owner v → B v := by
  classical
  obtain ⟨f, fi, fok⟩ := feas
  let X := {v : V // Core edge owner v ∧ ¬ B v}
  let g (x : X) := (closed x.val x.property.1).choose
  have hg (x : X) : owner x.val = some (g x) := (closed x.val x.property.1).choose_spec
  have rg (x : X) : Reach edge owner (g x) := by
    obtain ⟨c, hc, hv⟩ := x.property.1
    exact .step hc hv (hg x)
  let d (x : X) : {c // External edge B c} :=
    ⟨g x, x.val, matchedEdge (hg x), x.property.2⟩
  let t (x : X) : X := ⟨f (d x), ⟨g x, rg x, (fok (d x)).1⟩, (fok (d x)).2⟩
  have ti : Function.Injective t := by
    intro x y h
    have hfg : f (d x) = f (d y) := congrArg Subtype.val h
    have hgg : g x = g y := congrArg Subtype.val (fi hfg)
    exact Subtype.ext (uniqueVar ((hg x).trans (congrArg some hgg)) (hg y))
  have ts := Finite.surjective_of_injective ti
  have externalHasOwner {c} (hr : Reach edge owner c) (he : External edge B c) :
      ∃ v, ¬ B v ∧ owner v = some c := by
    let e : {c // External edge B c} := ⟨c, he⟩
    let y : X := ⟨f e, ⟨c, hr, (fok e).1⟩, (fok e).2⟩
    obtain ⟨x, hx⟩ := ts y
    have hfe : f (d x) = f e := congrArg Subtype.val hx
    have hgc : g x = c := congrArg Subtype.val (fi hfe)
    exact ⟨x.val, x.property.2, (hg x).trans (congrArg some hgc)⟩
  have inside {c} (hr : Reach edge owner c) : ¬ External edge B c := by
    induction hr with
    | free c h =>
      intro he
      obtain ⟨v, _, hv⟩ := externalHasOwner (.free c h) he
      exact h v hv
    | @step c v d hc hv hd ih =>
      intro he
      obtain ⟨w, hw, hwd⟩ := externalHasOwner (.step hc hv hd) he
      exact ih ⟨v, hv, (uniqueVar hd hwd) ▸ hw⟩
  rintro v ⟨c, hc, hv⟩
  by_contra h
  exact inside hc ⟨v, hv, h⟩

omit [Finite V] in
theorem feasible_core (edge : C → V → Prop) (owner : V → Option C)
    (matchedEdge : ∀ {v c}, owner v = some c → edge c v) :
    Feasible edge (Core edge owner) := by
  classical
  have hasOwner (c : {c // External edge (Core edge owner) c}) :
      ∃ v, owner v = some c.val := by
    by_contra! h
    obtain ⟨v, hv, hout⟩ := c.property
    exact hout ⟨c.val, .free _ h, hv⟩
  let f (c : {c // External edge (Core edge owner) c}) := (hasOwner c).choose
  have hf (c) : owner (f c) = some c.val := (hasOwner c).choose_spec
  refine ⟨f, ?_, ?_⟩
  · intro c d h
    exact Subtype.ext (Option.some.inj ((hf c).symm.trans ((congrArg owner h).trans (hf d))))
  · intro c
    refine ⟨matchedEdge (hf c), ?_⟩
    rintro ⟨d, hd, hedge⟩
    obtain ⟨v, hv, hout⟩ := c.property
    exact hout ⟨c.val, .step hd hedge (hf c), hv⟩

end HallLeastCore
