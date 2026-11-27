import ExactPlaneQuotientRows

namespace ExactPlaneEagerField
open ExactPlaneBinaryArithmetic (F Word)
open ExactPlaneNumericalRows (words dot)
open scoped BigOperators

abbrev W (r : Nat) := Vector F r
def read (x : W r) : Word r := fun j => x[j]
def store (x : Word r) : W r := Vector.ofFn x

@[simp] theorem read_store (x : Word r) : read (store x)=x := by
  funext j
  simp [read,store]

/-- The next state and all previous states in increasing exponent order. -/
def prefixTable (f : α→α) (x : α) : Nat → α × Array α
  | 0 => (x,#[])
  | n+1 =>
    let st := prefixTable f x n
    (f st.1,st.2.push st.1)

theorem prefix_eq (f : α→α) (x : α) (g : Nat→α) (base : g 0=x)
    (next : ∀ j,g (j+1)=f (g j)) (n : Nat) :
    prefixTable f x n = (g n,((List.range n).map g).toArray) := by
  induction n with
  | zero => simp [prefixTable,base]
  | succ n ih => simp [prefixTable,ih,next,List.range_succ]

theorem at_prefix (f : α→α) (x : α) (g : Nat→α) (base : g 0=x)
    (next : ∀ j,g (j+1)=f (g j)) {n : Nat} (i : Fin n) :
    (prefixTable f x n).2.getD i.val x = g i.val := by
  rw [prefix_eq f x g base next n]
  simp [Array.getD,i.isLt]

def step (c x : W r) : W r := store (ExactPlaneBinaryArithmetic.step (read c) (read x))

theorem read_step (c x : W r) :
    read (step c x)=ExactPlaneBinaryArithmetic.step (read c) (read x) := read_store _

def shifts (c x : W r) : Nat→W r
  | 0 => x
  | n+1 => step c (shifts c x n)

theorem read_shifts (c x : W r) (n : Nat) :
    read (shifts c x n)=ExactPlaneBinaryArithmetic.shifts (read c) (read x) n := by
  induction n with
  | zero => rfl
  | succ n ih => rw [shifts,read_step,ih,ExactPlaneBinaryArithmetic.shifts]

def mul (c x y : W r) : W r :=
  let powers := (prefixTable (step c) y r).2
  store (fun j => ∑ i : Fin r,read x i * read (powers.getD i.val y) j)

theorem read_mul (c x y : W r) :
    read (mul c x y)=ExactPlaneBinaryArithmetic.mul (read c) (read x) (read y) := by
  unfold mul ExactPlaneBinaryArithmetic.mul
  rw [read_store]
  funext j
  simp only [Finset.sum_apply,Pi.smul_apply,smul_eq_mul]
  apply Finset.sum_congr rfl
  intro i _
  rw [at_prefix (step c) y (shifts c y) rfl (fun _ => rfl) i,read_shifts]

def one (r : Nat) : W r := store (ExactPlaneBinaryArithmetic.unit 0)
def power (c x : W r) : Nat→W r
  | 0 => one r
  | n+1 => mul c (power c x n) x

theorem read_power (c x : W r) (n : Nat) :
    read (power c x n)=ExactPlaneBinaryArithmetic.power (read c) (read x) n := by
  induction n with
  | zero => exact read_store _
  | succ n ih => rw [power,read_mul,ih,ExactPlaneBinaryArithmetic.power]

def rowsAt (m : Nat) (c x : W r) (duals : List (Word r)) : List (Vector F m) :=
  let initial := one r
  let table := (prefixTable (fun a => mul c a x) initial m).2
  duals.map fun t => Vector.ofFn (fun i : Fin m => dot t (read (table.getD i.val initial)))

theorem rowsAt_eq (m : Nat) (c x : W r) (duals : List (Word r)) :
    rowsAt m c x duals = duals.map (fun t => Vector.ofFn (fun i : Fin m =>
      dot t (ExactPlaneBinaryArithmetic.power (read c) (read x) i.val))) := by
  unfold rowsAt
  apply List.map_congr_left
  intro t _
  congr 1
  funext i
  rw [at_prefix (fun a => mul c a x) (one r) (power c x) rfl (fun _ => rfl) i,read_power]

def seedRows (m : Nat) (c : W r) : List (Vector F m) :=
  let ws := words r
  ws.flatMap fun x => rowsAt m c (store x) ws

theorem seedRows_eq (m : Nat) (c : W r) :
    seedRows m c = ExactPlaneQuotientRows.seedRows m (read c) := by
  simp only [seedRows,ExactPlaneQuotientRows.seedRows,ExactPlaneNumericalRows.rows,rowsAt_eq,read_store]

#print axioms seedRows_eq
end ExactPlaneEagerField
