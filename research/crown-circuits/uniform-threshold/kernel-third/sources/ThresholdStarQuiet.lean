import ThresholdStarBypass
namespace ThresholdStarBypass
open ThresholdOrGroups
def Away (v : Nat) (f g : Env) := ∀ j,j≠v → f j=g j
/-- Only the selected neighbor root may expose x. The forced U is ignored.
A consumer of the root is an AND blocked on its *other* pin in the base row. -/
def Shield (u x v : Nat) (f : Env) (b : Block) : Prop :=
  b.out=u ∨ b.out=v ∨ match b with
  | .meet _ l r => (l≠v ∧ r≠v) ∨ (l=v ∧ r≠v ∧ f r=false) ∨ (r=v ∧ l≠v ∧ f l=false)
  | .group _ t => x∉t.raws ∧ v∉t.exts

def Shielded (u x v : Nat) (sel : Nat → Bool) (raw : Env) :
    List Block → Env → Prop
  | [],_ => True
  | b::bs,f => Shield u x v f b ∧
      Shielded u x v sel raw bs (put f b.out (row u sel true raw f b))

theorem any_away (xs : List Nat) (x : Nat) (f g : Env)
    (h : Away x f g) (absent : x∉xs) : xs.any f=xs.any g := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
    have ne : a≠x := by intro eq; simp [eq] at absent
    have tail : x∉xs := fun hx => absent (by simp [hx])
    simp only [List.any_cons,h a ne,ih tail]

private theorem shield_row (u x v : Nat) (sel : Nat → Bool) (src dst f g : Env)
    (rawEq : Away x src dst) (prev : Away v f g) (b : Block)
    (ok : Shield u x v f b) (out : b.out≠v) :
    row u sel true src f b=row u sel true dst g b := by
  rcases ok with forced|exempt|localok
  · simp [row,forced]
  · exact False.elim (out exempt)
  · cases b with
    | group p t =>
      obtain ⟨r,e⟩ := localok
      simp only [row,any_away _ _ _ _ rawEq r,any_away _ _ _ _ prev e]
    | meet w l r =>
      rcases localok with ⟨hl,hr⟩|⟨_,hr,off⟩|⟨_,hl,off⟩
      · simp [row,prev l hl,prev r hr]
      · have off' := (prev r hr).symm.trans off
        simp [row,off,off']
      · have off' := (prev l hl).symm.trans off
        simp [row,off,off']

theorem shielded_quiet (u x v : Nat) (sel : Nat → Bool) (src dst : Env)
    (rawEq : Away x src dst) (bs : List Block) (f g : Env)
    (prev : Away v f g) (ok : Shielded u x v sel src bs f) :
    Away v (run u sel true src bs f) (run u sel true dst bs g) := by
  induction bs generalizing f g with
  | nil => exact prev
  | cons b bs ih =>
    apply ih _ _ _ ok.2
    intro j jv
    by_cases eq : j=b.out
    · subst j; simpa [put] using shield_row u x v sel src dst f g rawEq prev b ok.1 jv
    · simpa [put,eq] using prev j jv

/-- No terminal tap reads the raw alias of a selected neighbor: its only
external reader is an AND. This excludes all group external lists, including
that neighbor's own list (which refers only to earlier wires). -/
def OutsideTaps (u v : Nat) (sel : Nat → Bool) : Block → Prop
  | .meet .. => True
  | .group _ t => t.out≠u → sel t.out=true → v∉t.exts

theorem shielded_taps (u x v : Nat) (sel : Nat → Bool) (src dst : Env)
    (rawEq : Away x src dst) (bs : List Block) (f g : Env) (prev : Away v f g)
    (ok : Shielded u x v sel src bs f) (outside : ∀ b∈bs, OutsideTaps u v sel b) :
    taps u sel src bs f=taps u sel dst bs g := by
  induction bs generalizing f g with
  | nil => rfl
  | cons b bs ih =>
    have sameTap : tap u sel f b=tap u sel g b := by
      have cut := outside b (by simp)
      cases b with
      | meet => rfl
      | group p t =>
        by_cases force : t.out=u <;> cases h : sel t.out <;> simp [tap,force,h]
        exact any_away t.exts v f g prev (cut force h)
    have newPrev : Away v (put f b.out (row u sel true src f b))
        (put g b.out (row u sel true dst g b)) := by
      intro j jv
      by_cases eq : j=b.out
      · subst j; simpa [put] using shield_row u x v sel src dst f g rawEq prev b ok.1 jv
      · simpa [put,eq] using prev j jv
    simp only [taps,sameTap,ih _ _ newPrev ok.2 (fun a ha => outside a (by simp [ha]))]

theorem shielded_promoted (u x v : Nat) (sel : Nat → Bool) (src dst : Env)
    (rawEq : Away x src dst) (bs : List Block) (f g : Env) (prev : Away v f g)
    (ok : Shielded u x v sel src bs f) (outside : ∀ b∈bs, OutsideTaps u v sel b)
    (out : Nat) (notAlias : out≠v) :
    (run u sel true src bs f out || taps u sel src bs f) =
      (run u sel true dst bs g out || taps u sel dst bs g) := by
  rw [shielded_quiet _ _ _ _ _ _ rawEq _ _ _ prev ok out notAlias,
    shielded_taps _ _ _ _ _ _ rawEq _ _ _ prev ok outside]

#print axioms shielded_promoted
#print axioms shielded_quiet
end ThresholdStarBypass
