import Mathlib.Tactic.DeriveFintype
import Mathlib.Data.Finset.Card

namespace ReadOnceLCA

inductive Op where | conj | disj
  deriving DecidableEq
instance : Fintype Op where
  elems := {.conj, .disj}
  complete x := by cases x <;> decide

inductive Tag where | empty | left | right | meet | join
  deriving DecidableEq
instance : Fintype Tag where
  elems := {.empty, .left, .right, .meet, .join}
  complete x := by cases x <;> decide

inductive Obs where | zero | one | left | right | meet | join
  deriving DecidableEq
instance : Fintype Obs where
  elems := {.zero, .one, .left, .right, .meet, .join}
  complete x := by cases x <;> decide


def Op.run : Op → Bool → Bool → Bool
  | .conj, x, y => x && y
  | .disj, x, y => x || y

def Obs.run : Obs → Bool → Bool → Bool
  | .zero, _, _ => false
  | .one, _, _ => true
  | .left, x, _ => x
  | .right, _, y => y
  | .meet, x, y => x && y
  | .join, x, y => x || y

/-- Abstract evaluation of monotone two-input truth tables. -/
def combine (op : Op) (p q : Obs) : Obs :=
  if op.run (p.run false false) (q.run false false) then .one
  else if !(op.run (p.run true true) (q.run true true)) then .zero
  else match op.run (p.run true false) (q.run true false),
             op.run (p.run false true) (q.run false true) with
    | true, true => .join
    | true, false => .left
    | false, true => .right
    | false, false => .meet

def merge (op : Op) : Tag → Tag → Option Tag
  | .empty, b => some b
  | a, .empty => some a
  | .left, .right | .right, .left => some (if op = .conj then .meet else .join)
  | _, _ => none

def allows : Tag → Obs → Bool
  | _, .zero | _, .one => true
  | .empty, _ => false
  | .left, .left | .right, .right => true
  | .meet, .left | .meet, .right | .meet, .meet => true
  | .join, .left | .join, .right | .join, .join => true
  | _, _ => false

set_option maxRecDepth 10000 in
set_option maxHeartbeats 1000000 in
private theorem local_closed : ∀ (op : Op) (a b : Tag) (p q : Obs),
    allows a p = true → allows b q = true →
    (merge op a b).all (fun c => allows c (combine op p q)) = true := by decide

private theorem local_eval : ∀ (op : Op) (p q : Obs) (x y : Bool),
    (combine op p q).run x y = op.run (p.run x y) (q.run x y) := by decide

inductive Formula (α : Type) where
  | left | right | param (i : α) | gate (op : Op) (l r : Formula α)

def Formula.eval {α} (env : α → Bool) (x y : Bool) : Formula α → Bool
  | .left => x
  | .right => y
  | .param i => env i
  | .gate op l r => op.run (l.eval env x y) (r.eval env x y)

def Formula.observe {α} (env : α → Bool) : Formula α → Obs
  | .left => .left
  | .right => .right
  | .param i => if env i then .one else .zero
  | .gate op l r => combine op (l.observe env) (r.observe env)

/-- Failure means at least one distinguished bit has repeated leaves. Parameter
    leaves can repeat freely, including in both subtrees. -/
def Formula.classify {α} : Formula α → Option Tag
  | .left => some .left
  | .right => some .right
  | .param _ => some .empty
  | .gate op l r => do merge op (← l.classify) (← r.classify)

theorem observe_eval {α} (t : Formula α) (env : α → Bool) (x y : Bool) :
    (t.observe env).run x y = t.eval env x y := by
  induction t with
  | left | right => rfl
  | param i => cases h : env i <;> simp [Formula.observe, Formula.eval, h, Obs.run]
  | gate op l r il ir => simpa [Formula.observe, Formula.eval, il, ir] using
      (local_eval op (l.observe env) (r.observe env) x y)

theorem observe_allowed {α} (t : Formula α) (env : α → Bool) :
    ∀ c, t.classify = some c → allows c (t.observe env) = true := by
  induction t with
  | left | right => intro c h; cases h; rfl
  | param i =>
    intro c h; cases h
    cases h' : env i <;> simp [Formula.observe, h', allows]
  | gate op l r il ir =>
    intro c h
    cases hl : l.classify with
    | none => simp [Formula.classify, hl] at h
    | some a =>
      cases hr : r.classify with
      | none => simp [Formula.classify, hl, hr] at h
      | some b =>
        have hg : merge op a b = some c := by simpa [Formula.classify, hl, hr] using h
        have hc := local_closed op a b (l.observe env) (r.observe env) (il _ hl) (ir _ hr)
        simpa [hg, Formula.observe] using hc

private theorem rigid_table : ∀ (c : Tag) (p q : Obs), allows c p = true →
    allows c q = true → (∀ x y, p.run x y = (x && y)) →
    (∀ x y, q.run x y = (x || y)) → False := by decide

/-- Changing parameter values cannot switch a read-once pair's binary
    connective from conjunction to disjunction. -/
theorem no_and_or {α} (t : Formula α) (c : Tag) (ro : t.classify = some c)
    (a b : α → Bool) (ha : ∀ x y, t.eval a x y = (x && y))
    (hb : ∀ x y, t.eval b x y = (x || y)) : False :=
  rigid_table c (t.observe a) (t.observe b) (observe_allowed t a c ro)
    (observe_allowed t b c ro) (fun x y => (observe_eval t a x y).trans (ha x y))
    (fun x y => (observe_eval t b x y).trans (hb x y))


def Tag.xCount : Tag → Nat
  | .empty | .right => 0
  | _ => 1

def Tag.yCount : Tag → Nat
  | .empty | .left => 0
  | _ => 1

def Formula.xCount {α} : Formula α → Nat
  | .left => 1
  | .gate _ l r => l.xCount + r.xCount
  | _ => 0

def Formula.yCount {α} : Formula α → Nat
  | .right => 1
  | .gate _ l r => l.yCount + r.yCount
  | _ => 0

private theorem merge_count : ∀ (op : Op) (a b : Tag),
    a.xCount + b.xCount ≤ 1 → a.yCount + b.yCount ≤ 1 →
    ∃ c : Tag, merge op a b = some c ∧ c.xCount = a.xCount + b.xCount ∧
      c.yCount = a.yCount + b.yCount := by decide

theorem classify_of_counts {α} (t : Formula α) :
    t.xCount ≤ 1 → t.yCount ≤ 1 → ∃ c, t.classify = some c ∧
      c.xCount = t.xCount ∧ c.yCount = t.yCount := by
  induction t with
  | left => exact fun _ _ => ⟨.left, rfl, rfl, rfl⟩
  | right => exact fun _ _ => ⟨.right, rfl, rfl, rfl⟩
  | param _ => exact fun _ _ => ⟨.empty, rfl, rfl, rfl⟩
  | gate op l r il ir =>
    intro hx hy
    change l.xCount + r.xCount ≤ 1 at hx
    change l.yCount + r.yCount ≤ 1 at hy
    obtain ⟨a, ha, ax, ay⟩ := il (by omega) (by omega)
    obtain ⟨b, hb, bx, by'⟩ := ir (by omega) (by omega)
    obtain ⟨c, hc, cx, cy⟩ := merge_count op a b (by omega) (by omega)
    exact ⟨c, by simp [Formula.classify, ha, hb, hc],
      by simpa [Formula.xCount, ax, bx] using cx,
      by simpa [Formula.yCount, ay, by'] using cy⟩

theorem no_and_or_of_occurrences {α} (t : Formula α)
    (hx : t.xCount ≤ 1) (hy : t.yCount ≤ 1) (a b : α → Bool)
    (ha : ∀ x y, t.eval a x y = (x && y))
    (hb : ∀ x y, t.eval b x y = (x || y)) : False := by
  obtain ⟨c, hc, _, _⟩ := classify_of_counts t hx hy
  exact no_and_or t c hc a b ha hb

end ReadOnceLCA
