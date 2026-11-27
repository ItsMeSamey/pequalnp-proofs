import ShoreCompiler
import ResidualProfiles

namespace OnePerShore.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Compiler

/-- Number of leaves in a nonempty monotone binary expression. -/
inductive Leaves {α : Type} : Ex α → ℕ → Prop where
  | var (a : α) : Leaves (.var a) 1
  | and {e f : Ex α} {i j} : Leaves e i → Leaves f j → Leaves (.and e f) (i+j)
  | or {e f : Ex α} {i j} : Leaves e i → Leaves f j → Leaves (.or e f) (i+j)

theorem Leaves.cost {α} {e : Ex α} {k} (h : Leaves e k) (w : α → ℕ) (N : ℕ) :
    (compile w e N).1.length + 1 = k := by
  induction h generalizing N with
  | var => simp [compile]
  | @and e f i j _ _ a b | @or e f i j _ _ a b =>
    simp only [compile,List.length_append,List.length_singleton]
    have l := a N
    have r := b (N + (compile w e N).1.length)
    omega

theorem Leaves.legal {α} {e : Ex α} {k} (h : Leaves e k) (w : α → ℕ) (N : ℕ) :
    ∀ g ∈ (compile w e N).1, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction h generalizing N with
  | var => simp [compile]
  | and _ _ a b | or _ _ a b =>
    intro g hg
    simp only [compile,List.mem_append,List.mem_singleton] at hg
    rcases hg with (h | h) | h
    · exact a _ g h
    · exact b _ g h
    · subst g; simp

abbrev Pred (n m : ℕ) := Fin n → Fin m → Bool
def readFlag {n m} (u : Fin n) (v : Fin m) : Fin n ⊕ Fin m → Bool
  | .inl i => decide (i=u)
  | .inr j => decide (j=v)

def Built {n m} (A : Pred n m) (k : ℕ) : Prop :=
  ∃ e : Ex (Fin n ⊕ Fin m), Leaves e k ∧ ∀ u v, e.eval (readFlag u v) = A u v

theorem Built.realize {n m k} {A : Pred n m} (b : Built A k) :
    RepSizeAtMost A (k-1) := by
  obtain ⟨e,h,sem⟩ := b
  let w : Fin n ⊕ Fin m → ℕ := Sum.elim Fin.val (fun j => n + j.val)
  let p := compile w e (n+m)
  refine ⟨⟨p.1,p.2⟩,h.legal w (n+m),?_,?_⟩
  · change (compile w e (n+m)).1.length ≤ k-1
    have := h.cost w (n+m); omega
  · intro u v
    have he : Rep (oneEach u v) w (readFlag u v) := by
      intro a
      cases a with
      | inl i =>
        simp [w,readFlag,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,i.isLt]
        omega
      | inr j =>
        simp [w,readFlag,oneEach,List.getD_eq_getElem?_getD]
    have hv := (compile_spec w e (oneEach u v) _ he).2
    rw [show (oneEach u v).length = n+m by simp [oneEach]] at hv
    exact hv.trans (sem u v)

theorem Built.and {n m a b} {A B : Pred n m} (ha : Built A a) (hb : Built B b) :
    Built (fun u v => A u v && B u v) (a+b) := by
  obtain ⟨e,h,s⟩ := ha; obtain ⟨f,h',s'⟩ := hb
  exact ⟨.and e f,.and h h',fun u v => by simp [Ex.eval,s,s']⟩

theorem Built.or {n m a b} {A B : Pred n m} (ha : Built A a) (hb : Built B b) :
    Built (fun u v => A u v || B u v) (a+b) := by
  obtain ⟨e,h,s⟩ := ha; obtain ⟨f,h',s'⟩ := hb
  exact ⟨.or e f,.or h h',fun u v => by simp [Ex.eval,s,s']⟩

open scoped BigOperators
noncomputable def anyOn {n m} {ι : Type} (s : Finset ι) (f : ι → Pred n m) : Pred n m := by
  classical
  exact fun u v => decide (∃ i ∈ s,f i u v = true)

theorem built_any {n m} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Pred n m) (k : ι → ℕ) :
    s.Nonempty → (∀ i ∈ s, Built (f i) (k i)) →
    Built (anyOn s f) (∑ i ∈ s,k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s fresh ih =>
    intro _ h
    have ha := h a (Finset.mem_insert_self ..)
    by_cases hs : s.Nonempty
    · have htail := ih hs (fun x hx => h _ (Finset.mem_insert_of_mem hx))
      have eq : anyOn (insert a s) f = (fun u v => f a u v || anyOn s f u v) := by
        funext u v; apply Bool.eq_iff_iff.mpr; simp [anyOn]
      simpa [eq,Finset.sum_insert,fresh] using ha.or htail
    · have := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have eq : anyOn {a} f = f a := by
        funext u v; apply Bool.eq_iff_iff.mpr; simp [anyOn]
      simpa [eq] using ha

end OnePerShore.Upper
