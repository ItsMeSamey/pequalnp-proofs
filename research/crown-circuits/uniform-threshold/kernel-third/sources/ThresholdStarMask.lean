import ThresholdStarQuiet
namespace ThresholdStarBypass
open ThresholdOrGroups

/-- A raw change at every group carrying x is masked either by the forced
root or by an already true external operand. No condition on AND pins. -/
def Mask (u x : Nat) (f : Env) (b : Block) : Prop :=
  b.out=u ∨ match b with
  | .meet .. => True
  | .group _ t => x∉t.raws ∨ t.exts.any f=true

def Masked (u x : Nat) (sel : Nat → Bool) (src : Env) : List Block → Env → Prop
  | [],_ => True
  | b::bs,f => Mask u x f b ∧ Masked u x sel src bs (put f b.out (row u sel false src f b))

private theorem row_mask (u x : Nat) (sel : Nat → Bool) (src dst f : Env)
    (eq : Away x src dst) (b : Block) (mask : Mask u x f b) :
    row u sel false src f b=row u sel false dst f b := by
  rcases mask with force|mask
  · simp [row,force]
  · cases b with
    | meet => rfl
    | group p t =>
      rcases mask with absent|already
      · have same := any_away t.raws x src dst eq absent
        simp only [row,same]
      · simp [row,already]

theorem masked_eq (u x : Nat) (sel : Nat → Bool) (src dst : Env)
    (eq : Away x src dst) (bs : List Block) (f : Env) (mask : Masked u x sel src bs f) :
    run u sel false src bs f=run u sel false dst bs f := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    change run _ _ _ _ bs _=run _ _ _ _ bs _
    rw [ih _ mask.2,row_mask u x sel src dst f eq b mask.1]

def rawFree (u x : Nat) (b : Block) : Prop :=
  b.out=u ∨ match b with
  | .meet .. => True
  | .group _ t => x∉t.raws

private theorem free_mask (u x : Nat) (f : Env) (b : Block) (h : rawFree u x b) : Mask u x f b := by
  rcases h with e|h
  · exact Or.inl e
  · apply Or.inr
    cases b with
    | meet => trivial
    | group => exact Or.inl h

theorem free_prefix (u x : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f : Env)
    (free : ∀ b∈bs, rawFree u x b) : Masked u x sel raw bs f := by
  induction bs generalizing f with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨free_mask u x f b (free b (by simp)),ih _ (fun a ha => free a (by simp [ha]))⟩

theorem masked_append (u x : Nat) (sel : Nat → Bool) (src : Env) (pre post : List Block) (f : Env) :
    Masked u x sel src (pre++post) f ↔
      Masked u x sel src pre f ∧ Masked u x sel src post (run u sel false src pre f) := by
  induction pre generalizing f with
  | nil => simp [Masked,run]
  | cons b pre ih => simp only [List.cons_append,Masked,run,ih,and_assoc]

/-- If the private neighbor's nonraw arm is already hot on a rejecting row,
turning on its raw x cannot produce an accepting row. Applies to arbitrary
prefix/suffix interleaving in the physical forest. -/
theorem clean_arm (u x : Nat) (sel : Nat → Bool) (src dst : Env) (eq : Away x src dst)
    (pre post : List Block) (pin : Nat) (t : Tree) (f : Env) (out : Nat)
    (before : ∀ b∈pre,rawFree u x b) (after : ∀ b∈post,rawFree u x b)
    (different : run u sel false src (pre ++ .group pin t :: post) f out ≠
      run u sel false dst (pre ++ .group pin t :: post) f out) :
    t.exts.any (run u sel false src pre f)=false := by
  cases h : t.exts.any (run u sel false src pre f) with
  | false => rfl
  | true =>
    have m : Masked u x sel src (pre ++ .group pin t :: post) f :=
      (masked_append ..).mpr ⟨free_prefix _ _ _ _ _ _ before,
        Or.inr (Or.inr h),free_prefix _ _ _ _ _ _ after⟩
    exact False.elim (different (congrFun (masked_eq _ _ _ _ _ eq _ _ m) out))

#print axioms clean_arm
end ThresholdStarBypass
