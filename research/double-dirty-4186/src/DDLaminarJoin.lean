import Q0Factor

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Laminar
open PEqualNP.CircuitLowerBounds PEqualNP.TopForm PEqualNP.MetaComplexity
open PEqualNP.Outside.L_meta_4186_aux.Q0
open Factor

/-- A restoration formula over surviving wires and symbolic true cofactors. -/
inductive Expr (n : ℕ) where
  | leaf (s : Option (Signal n))
  | gate (andGate : Bool) (left right : Expr n)

namespace Expr

def val {n : ℕ} : Expr n → Signal n
  | .leaf s => denotation s
  | .gate op a b => join op a.val b.val

def size {n : ℕ} : Expr n → ℕ
  | .leaf _ => 0
  | .gate _ a b => a.size + b.size + 1

def available {n : ℕ} (p : Pack n) : Expr n → Prop
  | .leaf s => physically (Available p) s
  | .gate _ a b => a.available p ∧ b.available p

private theorem mono {n : ℕ} {p q : Pack n} (keep : ∀ s, Available p s → Available q s)
    (e : Expr n) (h : e.available p) : e.available q := by
  induction e with
  | leaf s => cases s with
    | none => trivial
    | some f => exact keep f h
  | gate _ a b ha hb => exact ⟨ha h.1,hb h.2⟩

private theorem combine {n : ℕ} (p : Pack n) (op : Bool) (a b : Option (Signal n))
    (ha : physically (Available p) a) (hb : physically (Available p) b) :
    ∃ (q : Pack n) (s : Option (Signal n)), q.gates.length ≤ p.gates.length+1 ∧
      (∀ f, Available p f → Available q f) ∧ physically (Available q) s ∧
      denotation s = join op (denotation a) (denotation b) := by
  cases a with
  | none =>
    cases op
    · exact ⟨p,none,by omega,fun _ h => h,trivial,by funext x; simp [denotation,join]⟩
    · exact ⟨p,b,by omega,fun _ h => h,hb,by funext x; simp [denotation,join]⟩
  | some f =>
    cases b with
    | none =>
      cases op
      · exact ⟨p,none,by omega,fun _ h => h,trivial,by funext x; simp [denotation,join]⟩
      · exact ⟨p,some f,by omega,fun _ h => h,ha,by funext x; simp [denotation,join]⟩
    | some h =>
      obtain ⟨q,cost,keep,out⟩ := emit_available p op ha hb
      exact ⟨q,some (join op f h),cost.le,keep,out,rfl⟩

theorem build {n : ℕ} (p : Pack n) (e : Expr n) (h : e.available p) :
    ∃ (q : Pack n) (s : Option (Signal n)), q.gates.length ≤ p.gates.length+e.size ∧
      (∀ f, Available p f → Available q f) ∧ physically (Available q) s ∧ denotation s = e.val := by
  induction e generalizing p with
  | leaf s => exact ⟨p,s,by simp [size],fun _ a => a,h,rfl⟩
  | gate op a b ia ib =>
    obtain ⟨pa,sa,ca,ka,va,ea⟩ := ia p h.1
    obtain ⟨pb,sb,cb,kb,vb,eb⟩ := ib pa (mono ka b h.2)
    have va' : physically (Available pb) sa := by
      cases sa with
      | none => trivial
      | some f => exact kb f va
    obtain ⟨q,s,cq,kq,vs,es⟩ := combine pb op sa sb va' vb
    exact ⟨q,s,by simp only [size]; omega,fun f x => kq f (kb f (ka f x)),vs,
      by rw [es,ea,eb]; rfl⟩

def addOrs {n : ℕ} (start : Expr n) : List (Option (Signal n)) → Expr n
  | [] => start
  | s::ss => addOrs (.gate false start (.leaf s)) ss

theorem size_addOrs {n : ℕ} (start : Expr n) (ss : List (Option (Signal n))) :
    (addOrs start ss).size = start.size+ss.length := by
  induction ss generalizing start with
  | nil => simp [addOrs]
  | cons s ss ih => simp [addOrs,ih,size] <;> omega

/-- Inner roots share x and y. Outer roots share y. -/
def nested {n : ℕ} (x y first : Option (Signal n)) (inner outer unaffected : List (Option (Signal n))) :
    Expr n :=
  addOrs (.gate true (.leaf y) (addOrs (.gate true (.leaf x) (addOrs (.leaf first) inner)) outer)) unaffected

theorem nested_size {n : ℕ} (x y first : Option (Signal n)) (i o u : List (Option (Signal n))) :
    (nested x y first i o u).size = i.length + o.length + u.length + 2 := by
  simp [nested,size_addOrs,size] <;> omega

/-- The two source factors occur in disjoint root groups. -/
def separate {n : ℕ} (x y f g : Option (Signal n)) (xs ys rest : List (Option (Signal n))) : Expr n :=
  addOrs (.gate false (.gate true (.leaf x) (addOrs (.leaf f) xs))
    (.gate true (.leaf y) (addOrs (.leaf g) ys))) rest

theorem separate_size {n : ℕ} (x y f g : Option (Signal n)) (xs ys rest : List (Option (Signal n))) :
    (separate x y f g xs ys rest).size = xs.length + ys.length + rest.length + 3 := by
  simp [separate,size_addOrs,size] <;> omega

theorem finish {n : ℕ} (p : Pack n) (e : Expr n) (h : e.available p)
    (hasFalse : ∃ x, e.val x = false) :
    ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = e.val ∧ D.size ≤ p.gates.length + e.size := by
  obtain ⟨q,s,cost,_,hv,ev⟩ := build p e h
  cases s with
  | none =>
    obtain ⟨x,hx⟩ := hasFalse
    have contra := congrFun ev x
    simp [denotation,hx] at contra
  | some f =>
    obtain ⟨w,hw⟩ := hv
    exact ⟨q.finish w,q.finish_ao2 w,funext fun x => (q.finish_fun w x).trans
      ((hw x).trans (congrFun ev x)),by simpa [Pack.finish_size] using cost⟩

end Expr
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Laminar
