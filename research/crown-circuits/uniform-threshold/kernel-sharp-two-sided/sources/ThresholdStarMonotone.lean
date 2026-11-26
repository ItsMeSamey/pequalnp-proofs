import ThresholdStarBypass
namespace ThresholdStarBypass
open ThresholdOrGroups
private theorem any_inc (xs : List Nat) {f g : Env} (h : Below f g)
    (on : xs.any f=true) : xs.any g=true := by
  obtain ⟨w,mem,hw⟩ := List.any_eq_true.mp on
  exact List.any_eq_true.mpr ⟨w,mem,h w hw⟩

theorem scan_monotone (u : Nat) (sel : Nat → Bool) (mode : Bool) (src dst : Env)
    (r : Below src dst) (bs : List Block) (f g : Env) (h : Below f g) :
    Below (run u sel mode src bs f) (run u sel mode dst bs g) := by
  induction bs generalizing f g with
  | nil => exact h
  | cons b bs ih =>
    apply ih
    intro j
    by_cases out : j=b.out
    · subst j
      simp only [put,ite_true]
      by_cases force : b.out=u
      · simp [row,force]
      cases b with
      | meet w x y =>
        change w≠u at force
        simpa [row,Block.out,force] using (fun z : f x=true ∧ f y=true => And.intro (h x z.1) (h y z.2))
      | group p t =>
        change t.out≠u at force
        have a := any_inc t.raws r
        have e := any_inc t.exts h
        cases val : mode && sel t.out <;> simp [row,Block.out,force,val] at * <;> grind
    · simpa [put,out] using h j

end ThresholdStarBypass

namespace ThresholdStarBypass
open ThresholdOrGroups

/-- Certification is local at each selected group's original, unbypassed
prefix. Under this condition no tap fires and all stored wires coincide. -/
def ArmsOff (u : Nat) (sel : Nat → Bool) (raw : Env) : List Block → Env → Prop
  | [],_ => True
  | b::bs,f => tap u sel f b=false ∧
      ArmsOff u sel raw bs (put f b.out (row u sel false raw f b))

theorem all_off (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f : Env)
    (off : ArmsOff u sel raw bs f) : taps u sel raw bs f=false := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    have eq : row u sel true raw f b=row u sel false raw f b := by
      have no := off.1
      cases b with
      | meet => rfl
      | group p t =>
        by_cases force : t.out=u <;> cases s : sel t.out <;> cases e : t.exts.any f <;>
          simp_all [row,tap,Block.out]
    simp only [taps,off.1,Bool.false_or,eq,ih _ off.2]

theorem all_off_of_split (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f : Env)
    (localOff : ∀ pre b post, bs=pre++b::post → tap u sel (run u sel false raw pre f) b=false) :
    ArmsOff u sel raw bs f := by
  induction bs generalizing f with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨localOff [] b bs rfl,ih _ ?_⟩
    intro pre a post eq
    exact localOff (b::pre) a post (by simp [eq])

/-- If original threshold-negative assignments have no original hot taps,
the physically evaluated terminal disjunction preserves all outputs. -/
theorem promoted_same (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block)
    (f : Env) (out : Nat)
    (negative : run u sel false raw bs f out=false → ArmsOff u sel raw bs f) :
    (run u sel true raw bs f out || taps u sel raw bs f)=run u sel false raw bs f out := by
  cases e : run u sel false raw bs f out with
  | false =>
    have off := all_off _ _ _ _ _ (negative e)
    rw [run_eq_of_no_tap _ _ _ _ _ off,e,off]; rfl
  | true =>
    cases h : run u sel true raw bs f out with
    | true => rfl
    | false =>
      rw [lost_caught _ _ _ _ _ _ e h]; rfl

#print axioms promoted_same
end ThresholdStarBypass
