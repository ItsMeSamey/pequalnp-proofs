import ThresholdOrPhysicalBook
import ThresholdStarPartners
namespace ThresholdStarBypass
open ThresholdOrGroups
abbrev Env := Nat → Bool
def put (f : Env) (w : Nat) (b : Bool) : Env := fun i => if i=w then b else f i
def row (u : Nat) (sel : Nat → Bool) (bypass : Bool) (raw f : Env) (b : Block) : Bool :=
  if b.out=u then true else match b with
  | .meet _ x y => f x && f y
  | .group _ t => t.raws.any raw || (!(bypass && sel t.out) && t.exts.any f)
def tap (u : Nat) (sel : Nat → Bool) (f : Env) : Block → Bool
  | .meet .. => false
  | .group _ t => decide (t.out≠u) && sel t.out && t.exts.any f
def run (u : Nat) (sel : Nat → Bool) (bypass : Bool) (raw : Env) :
    List Block → Env → Env
  | [],f => f
  | b::bs,f => run u sel bypass raw bs (put f b.out (row u sel bypass raw f b))
def taps (u : Nat) (sel : Nat → Bool) (raw : Env) : List Block → Env → Bool
  | [],_ => false
  | b::bs,f => tap u sel f b ||
      taps u sel raw bs (put f b.out (row u sel true raw f b))

private theorem local_same (u : Nat) (sel : Nat → Bool) (raw f : Env) (b : Block)
    (off : tap u sel f b=false) :
    row u sel true raw f b=row u sel false raw f b := by
  cases b with
  | meet w x y => rfl
  | group p t =>
    by_cases forced : t.out=u <;> cases h : sel t.out <;> cases e : t.exts.any f <;>
      simp_all [row,tap,Block.out]

/-- Bypassed and original ledgers agree whenever all new taps are off. -/
theorem run_eq_of_no_tap (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f : Env)
    (off : taps u sel raw bs f=false) : run u sel true raw bs f=run u sel false raw bs f := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    have cut : tap u sel f b=false := by
      cases h : tap u sel f b <;> simp_all [taps]
    have tail : taps u sel raw bs (put f b.out (row u sel true raw f b))=false := by
      simpa [taps,cut] using off
    change run _ _ _ _ bs _=run _ _ _ _ bs _
    rw [ih _ tail, local_same u sel raw f b cut]

def Below (f g : Env) := ∀ w, f w=true → g w=true
private theorem any_mono (xs : List Nat) (f g : Env) (h : Below f g)
    (on : xs.any f=true) : xs.any g=true := by
  obtain ⟨w,mem,hw⟩ := List.any_eq_true.mp on
  exact List.any_eq_true.mpr ⟨w,mem,h w hw⟩
private theorem put_mono (f g : Env) (w : Nat) (x y : Bool)
    (fg : Below f g) (xy : x=true → y=true) : Below (put f w x) (put g w y) := by
  intro i
  by_cases eq : i=w
  · simpa [put,eq] using xy
  · simpa [put,eq] using fg i
private theorem row_mono (u : Nat) (sel : Nat → Bool) (raw f g : Env) (b : Block)
    (fg : Below f g) : row u sel true raw f b=true → row u sel false raw g b=true := by
  cases b with
  | meet w x y =>
    by_cases h : w=u
    · simp [row,Block.out,h]
    · simpa [row,Block.out,h] using (fun v : f x=true ∧ f y=true => And.intro (fg x v.1) (fg y v.2))
  | group p t =>
    by_cases h : t.out=u
    · simp [row,Block.out,h]
    · have mono := any_mono t.exts f g fg
      cases e : t.raws.any raw <;> cases s : sel t.out <;>
        simp_all [row,Block.out] <;> grind
theorem run_below (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f g : Env)
    (fg : Below f g) : Below (run u sel true raw bs f) (run u sel false raw bs g) := by
  induction bs generalizing f g with
  | nil => exact fg
  | cons b bs ih => exact ih _ _ (put_mono _ _ _ _ _ fg (row_mono u sel raw f g b fg))
theorem lost_caught (u : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block)
    (f : Env) (out : Nat) (old : run u sel false raw bs f out=true)
    (newOff : run u sel true raw bs f out=false) : taps u sel raw bs f=true := by
  cases eq : taps u sel raw bs f with
  | true => rfl
  | false => rw [run_eq_of_no_tap u sel raw bs f eq,old] at newOff; contradiction
#print axioms lost_caught
#print axioms run_below
end ThresholdStarBypass
