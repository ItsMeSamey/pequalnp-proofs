import ExactPlaneEagerField
namespace ExactPlaneSeedWork
open ExactPlaneEagerField
open ExactPlaneBinaryArithmetic (Word F)
open ExactPlaneNumericalRows (words dot length_words)
open scoped BigOperators

/-- Each call to the supplied iterator is charged once, including the final
advance, whose value is omitted when callers retain only the table. -/
def advances (f : α→α) (a : α) : Nat → (α × Array α) × Nat
  | 0 => ((a,#[]),0)
  | n+1 =>
    let ((v,table),k) := advances f a n
    ((f v,table.push v),k+1)

theorem advances_eq (f : α→α) (a : α) (n : Nat) :
    advances f a n=(prefixTable f a n,n) := by
  induction n with
  | zero => rfl
  | succ n ih => simp [advances,prefixTable,ih]

/-- Materialize each evaluation together with one charge; projecting or
summing the charge reads the stored entry without evaluating it again. -/
def emit (f : Fin m → F) : Vector F m × Nat :=
  let a := Vector.ofFn (fun i => (f i,(1:Nat)))
  (Vector.ofFn (fun i : Fin m => a[i].1), ∑ i : Fin m, a[i].2)

theorem emit_eq (f : Fin m → F) : emit f=(Vector.ofFn f,m) := by
  simp [emit]

def dualRows (table : Array (W r)) (initial : W r) (m : Nat) :
    List (Word r) → List (Vector F m) × Nat
  | [] => ([],0)
  | t::ts =>
    let row := emit (fun i : Fin m => dot t (read (table.getD i.val initial)))
    let tail := dualRows table initial m ts
    (row.1 :: tail.1,row.2 + tail.2)

theorem dualRows_eq (table : Array (W r)) (initial : W r) (m : Nat) (ts : List (Word r)) :
    dualRows table initial m ts =
      (ts.map (fun t => Vector.ofFn (fun i : Fin m => dot t (read (table.getD i.val initial)))),
       ts.length*m) := by
  induction ts with
  | nil => simp [dualRows]
  | cons t ts ih => simp [dualRows,emit_eq,ih,Nat.add_mul,Nat.add_comm]

structure Output (m : Nat) where
  rows : List (Vector F m)
  multiplications : Nat
  dots : Nat
  tables : Nat

def run (c : W r) (m : Nat) (duals : List (Word r)) :
    List (Word r) → Output m
  | [] => ⟨[],0,0,0⟩
  | x::xs =>
    let initial := one r
    let base := store x
    let cache := advances (fun a => mul c a base) initial m
    let out := dualRows cache.1.2 initial m duals
    let tail := run c m duals xs
    ⟨out.1 ++ tail.rows,cache.2 + tail.multiplications,out.2 + tail.dots,tail.tables+1⟩

theorem run_eq (c : W r) (m : Nat) (duals xs : List (Word r)) :
    run c m duals xs = ⟨xs.flatMap (fun x => rowsAt m c (store x) duals),
      xs.length*m, xs.length*(duals.length*m),xs.length⟩ := by
  induction xs with
  | nil => simp [run]
  | cons x xs ih =>
    simp [run,advances_eq,dualRows_eq,ih,rowsAt,Nat.add_mul,Nat.add_comm]

def counted (m : Nat) (c : W r) := let ws := words r; run c m ws ws

theorem counted_eq (m : Nat) (c : W r) :
    counted m c = ⟨seedRows m c,(2^r)*m,(2^r)^2*m,2^r⟩ := by
  simp only [counted,run_eq,seedRows,length_words,pow_two,Nat.mul_assoc]

#print axioms counted_eq
end ExactPlaneSeedWork
