import DDLaminarJoin
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Laminar
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4186_aux.Q0
open Factor
/-- None here is an empty OR group; a leaf may separately carry symbolic true. -/
abbrev Group (n : ℕ) := Option (Expr n)
namespace Group
def mass {n : ℕ} : Group n → ℕ
  | none => 0
  | some e => e.size+1
def eval {n : ℕ} (x : Fin n → Bool) : Group n → Prop
  | none => False
  | some e => e.val x = true
def ok {n : ℕ} (p : Pack n) : Group n → Prop
  | none => True
  | some e => e.available p
def merge {n : ℕ} : Group n → Group n → Group n
  | none, q => q
  | some e, none => some e
  | some e, some f => some (.gate false e f)
def restore {n : ℕ} (s : Option (Signal n)) : Group n → Group n
  | none => none
  | some e => some (.gate true (.leaf s) e)
theorem mass_merge {n : ℕ} (a b : Group n) : mass (merge a b) = mass a + mass b := by
  cases a <;> cases b <;> simp [merge,mass,Expr.size] <;> omega
theorem mass_restore {n : ℕ} (s : Option (Signal n)) (a : Group n) :
    mass (restore s a) ≤ mass a + 1 := by cases a <;> simp [restore,mass,Expr.size]
theorem eval_merge {n : ℕ} (x : Fin n → Bool) (a b : Group n) :
    eval x (merge a b) ↔ eval x a ∨ eval x b := by
  cases a <;> cases b <;> simp [merge,eval,Expr.val,join]
theorem eval_restore {n : ℕ} (x : Fin n → Bool) (s : Option (Signal n)) (a : Group n) :
    eval x (restore s a) ↔ denotation s x = true ∧ eval x a := by
  cases a <;> simp [restore,eval,Expr.val,join]
theorem ok_merge {n : ℕ} (p : Pack n) (a b : Group n) (ha : ok p a) (hb : ok p b) :
    ok p (merge a b) := by cases a <;> cases b <;> simp_all [ok,merge,Expr.available]
theorem ok_restore {n : ℕ} (p : Pack n) (s : Option (Signal n)) (a : Group n)
    (hs : physically (Available p) s) (ha : ok p a) : ok p (restore s a) := by
  cases a <;> simp_all [ok,restore,Expr.available]
def ofList {n : ℕ} (slot : ℕ → Option (Signal n)) : List ℕ → Group n
  | [] => none
  | i::is => merge (some (.leaf (slot i))) (ofList slot is)
theorem mass_list {n : ℕ} (slot : ℕ → Option (Signal n)) (L : List ℕ) :
    mass (ofList slot L) = L.length := by
  induction L with
  | nil => rfl
  | cons i is ih =>
    rw [ofList,mass_merge,ih]
    change 1 + is.length = is.length + 1
    omega
theorem eval_list {n : ℕ} (x : Fin n → Bool) (slot : ℕ → Option (Signal n)) (L : List ℕ) :
    eval x (ofList slot L) ↔ ∃ i ∈ L, denotation (slot i) x = true := by
  induction L with
  | nil => simp [ofList,eval]
  | cons i is ih =>
    rw [ofList,eval_merge,ih]
    change denotation (slot i) x = true ∨ _ ↔ _
    simp only [List.mem_cons]
    aesop
theorem ok_list {n : ℕ} (p : Pack n) (slot : ℕ → Option (Signal n)) (L : List ℕ)
    (h : ∀ i ∈ L, physically (Available p) (slot i)) : ok p (ofList slot L) := by
  induction L with
  | nil => trivial
  | cons i is ih =>
    apply ok_merge
    · exact h i (by simp)
    · exact ih fun j hj => h j (by simp [hj])
end Group
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Laminar
