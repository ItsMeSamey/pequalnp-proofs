import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.EquivFin
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD
import PEqualNP.Defs.Represents

/-! A monotone fan-in-two circuit representing the 12-crown on one-hot row and column inputs requires at least 31 OR gates. The proof treats conjunctions as free. -/

namespace FreeAndNet
abbrev Product (α : Type) := Option (List α)
def pval {α : Type} (v : α → Bool) (p : Product α) := p.elim false (fun a => a.all v)

/-- The atom "none" in a tail denotes the newly computed OR. -/
inductive Net : Type → Type 1 where
  | out {α : Type} (value : Product α) : Net α
  | gate {α : Type} (left right : List α) (tail : Net (Option α)) : Net α

def Net.eval {α} (v : α → Bool) : Net α → Bool
  | .out p => pval v p
  | .gate a b tail => tail.eval (fun z => z.elim (a.all v || b.all v) v)

def Net.cost {α} : Net α → Nat
  | .out _ => 0
  | .gate _ _ tail => tail.cost + 1

def substProduct {α β : Type} (s : α → Product β) : List α → Product β
  | [] => some []
  | i :: xs => match s i, substProduct s xs with
    | some a, some b => some (a ++ b)
    | _,_ => none

theorem pval_subst {α β : Type} (s : α → Product β) (a : List α) (v : β → Bool) :
    pval v (substProduct s a) = a.all (fun i => pval v (s i)) := by
  induction a with
  | nil => rfl
  | cons x xs ih =>
    rw [List.all_cons,← ih, substProduct]
    cases s x <;> cases substProduct s xs <;> simp [pval]

def liftP {α : Type} : Product α → Product (Option α) := Option.map (List.map some)

def specialize {α β : Type} (s : α → Product β) : Net α → Net β
  | .out p => .out (p.bind (substProduct s))
  | .gate a b t =>
    match substProduct s a, substProduct s b with
    | none,p | p,none => specialize (fun z => z.elim p s) t
    | some u,some v => .gate u v (specialize (fun z => z.elim (some [none]) (fun i => liftP (s i))) t)

end FreeAndNet

namespace FreeAndNet

theorem pval_lift {α} (v : α → Bool) (h : Bool) (p : Product α) :
    pval (fun z => z.elim h v) (liftP p) = pval v p := by
  cases p <;> simp [liftP,pval,List.all_map,Function.comp_def]

theorem eval_specialize {α β : Type} (s : α → Product β) (t : Net α) (v : β → Bool) :
    (specialize s t).eval v = t.eval (fun i => pval v (s i)) := by
  induction t generalizing β with
  | out p => cases p with
    | none => rfl
    | some a => exact pval_subst s a v
  | gate a b t ih =>
    simp only [specialize, Net.eval]
    rw [← pval_subst s a v, ← pval_subst s b v]
    cases ha : substProduct s a <;> cases hb : substProduct s b <;>
      simp only [Net.eval,ih] <;> congr 1 <;> funext z <;> cases z <;>
        first | apply pval_lift | simp [pval]

noncomputable section
open Classical in
def hits {α : Type} (i : α) : Net α → Nat
  | .out _ => 0
  | .gate a b t => hits (some i) t + if i ∈ a ∨ i ∈ b then 1 else 0

theorem subst_none {α β : Type} {s : α → Product β} {i : α} (h : s i = none)
    (a : List α) (m : i ∈ a) : substProduct s a = none := by
  induction a with
  | nil => simp at m
  | cons x xs ih =>
    simp only [List.mem_cons] at m
    rcases m with rfl|m
    · simp [substProduct,h]
    · simp [substProduct,ih m]

/-- Every OR mentioning a killed atom in either operand can be removed, even
if different retained ORs reuse old subexpressions. -/
theorem specialize_saves {α β : Type} (i : α) (s : α → Product β)
    (hs : s i = none) (t : Net α) : (specialize s t).cost + hits i t ≤ t.cost := by
  classical
  induction t generalizing β with
  | out => simp [specialize,hits,Net.cost]
  | gate a b t ih =>
    simp only [specialize,hits,Net.cost]
    generalize ha : substProduct s a = pa
    generalize hb : substProduct s b = pb
    cases pa <;> cases pb
    all_goals simp only [Net.cost]
    have simple (p : Product β) : (specialize (fun z => z.elim p s) t).cost +
        (hits (some i) t + (if i ∈ a ∨ i ∈ b then 1 else 0)) ≤ t.cost + 1 := by
      have h := ih (some i) (fun z => z.elim p s) hs
      split <;> omega
    exact simple none
    next vs =>
      have h := ih (some i) (fun z => z.elim (some vs) s) hs
      split <;> omega
    next us =>
      have h := ih (some i) (fun z => z.elim (some us) s) hs
      split <;> omega
    next us vs =>
      have h := ih (some i) (fun z => z.elim (some [none]) (fun j => liftP (s j)))
        (by simp [hs,liftP] : liftP (s i) = none)
      have hn : ¬ (i ∈ a ∨ i ∈ b) := by
        rintro (h|h)
        · rw [subst_none hs a h] at ha; contradiction
        · rw [subst_none hs b h] at hb; contradiction
      simp only [hn,reduceIte,Nat.add_zero]; omega
end
end FreeAndNet

namespace FreeAndNet

def outUses {α} (i : α) : Net α → Prop
  | .out p => ∃ xs, p = some xs ∧ i ∈ xs
  | .gate _ _ t => outUses (some i) t

theorem outZeros {α} (t : Net α) (i : α) (h : outUses i t) (v : α → Bool)
    (hv : v i = false) : t.eval v = false := by
  induction t with
  | out p =>
    obtain ⟨xs,rfl,hm⟩ := h
    simp only [Net.eval,pval,Option.elim_some]
    by_contra! he
    have htt : xs.all v = true := by cases hh : xs.all v <;> simp_all
    have z := List.all_eq_true.mp htt i hm
    simp_all
  | gate a b t ih => exact ih (some i) h _ hv

private theorem all_eq {α : Type} {xs : List α} {v w : α → Bool} (h : ∀ i ∈ xs, v i = w i) : xs.all v = xs.all w := by
  induction xs with
  | nil => rfl
  | cons i xs ih =>
    simp only [List.all_cons, h i (by simp), ih (fun j hj => h j (by simp [hj]))]

theorem eval_congr_used {α} (t : Net α) (v w : α → Bool)
    (agree : ∀ i, 0 < hits i t ∨ outUses i t → v i = w i) : t.eval v = t.eval w := by
  induction t with
  | out p =>
    cases p with
    | none => rfl
    | some xs =>
      apply all_eq
      intro i h; exact agree _ (Or.inr ⟨_,rfl,h⟩)
  | gate a b t ih =>
    have used (i) (h : i ∈ a ∨ i ∈ b) : v i = w i :=
      agree _ (Or.inl (by simp [hits,h]))
    have ea : a.all v = a.all w := all_eq (fun i hi => used i (Or.inl hi))
    have eb : b.all v = b.all w := all_eq (fun i hi => used i (Or.inr hi))
    apply ih
    intro i h
    cases i with
    | none => simp [ea,eb]
    | some i =>
      apply agree
      rcases h with h|h
      · left; simp only [hits]; omega
      · exact Or.inr h
end FreeAndNet

namespace CrownMixed
open FreeAndNet

structure Naming (I α : Type) where
  row : I → α
  col : I → α
  row_inj : Function.Injective row
  col_inj : Function.Injective col
  same : ∀ {i j}, row i = col j → i=j

namespace Naming
variable {I α : Type}

def val [DecidableEq α] (N : Naming I α) (i j : I) (a : α) : Bool :=
  decide (a=N.row i ∨ a=N.col j)

def Rep [DecidableEq α] [DecidableEq I] (N : Naming I α) (t : Net α) : Prop :=
  ∀ i j, t.eval (N.val i j) = decide (i≠j)

def pairs [Fintype I] [DecidableEq α] (N : Naming I α) : Nat :=
  (Finset.univ.filter (fun i => N.row i = N.col i)).card

def remove (N : Naming I α) (i : I) : Naming {j : I // j≠i} α where
  row j := N.row j.val
  col j := N.col j.val
  row_inj := fun _ _ h => Subtype.ext (N.row_inj h)
  col_inj := fun _ _ h => Subtype.ext (N.col_inj h)
  same := fun h => Subtype.ext (N.same h)

end Naming
end CrownMixed

namespace FreeAndNet

theorem specialize_cost {α β : Type} (s : α → Product β) (t : Net α) :
    (specialize s t).cost ≤ t.cost := by
  induction t generalizing β with
  | out => rfl
  | gate a b t ih =>
    unfold specialize
    generalize substProduct s a = pa
    generalize substProduct s b = pb
    cases pa <;> cases pb <;> simp only [Net.cost]
    all_goals first | exact Nat.succ_le_succ (ih _) | exact Nat.le_succ_of_le (ih _)

theorem delete_first_of_product {α : Type} (a b : List α) (tail : Net (Option α))
    (p : Product α) (hp : ∀ v, pval v p = (a.all v || b.all v)) :
    ∃ u : Net α, (∀ v, u.eval v = (Net.gate a b tail).eval v) ∧
      u.cost < (Net.gate a b tail).cost := by
  let s : Option α → Product α := fun x => x.elim p (fun i => some [i])
  refine ⟨specialize s tail, ?_, Nat.lt_succ_of_le (specialize_cost s tail)⟩
  intro v
  rw [eval_specialize]
  apply congrArg (fun f => tail.eval f)
  funext x
  cases x with
  | none => exact hp v
  | some i => simp [s,pval]

theorem delete_degenerate_first {α : Type} [DecidableEq α] (a b : List α) (tail : Net (Option α))
    (h : a = [] ∨ b = [] ∨ (a.toFinset ∪ b.toFinset).card ≤ 1) :
    ∃ u : Net α, (∀ v, u.eval v = (Net.gate a b tail).eval v) ∧
      u.cost < (Net.gate a b tail).cost := by
  rcases h with rfl|rfl|h
  · apply delete_first_of_product _ _ _ (some [])
    simp [pval]
  · apply delete_first_of_product _ _ _ (some [])
    simp [pval]
  cases a with
  | nil => apply delete_first_of_product _ _ _ (some []); simp [pval]
  | cons x xs =>
    cases b with
    | nil => apply delete_first_of_product _ _ _ (some []); simp [pval]
    | cons y ys =>
      have allsame := Finset.card_le_one.mp h
      have hx : x ∈ (x::xs).toFinset ∪ (y::ys).toFinset := by simp
      have eqx (i : α) (hi : i ∈ (x::xs) ∨ i ∈ (y::ys)) : i = x :=
        allsame i (by simpa only [Finset.mem_union,List.mem_toFinset] using hi) x hx
      apply delete_first_of_product _ _ _ (some [x])
      intro v
      have aa : (x::xs).all v = v x := by
        cases hv : v x with
        | false => simp [hv]
        | true => exact List.all_eq_true.mpr (fun i hi => (eqx i (.inl hi)) ▸ hv)
      have bb : (y::ys).all v = v x := by
        cases hv : v x with
        | false => simp [List.all_cons,eqx y (.inr (by simp)),hv]
        | true => exact List.all_eq_true.mpr (fun i hi => (eqx i (.inr hi)) ▸ hv)
      rw [aa,bb]
      simp [pval]
end FreeAndNet

namespace FreeAndNet

def eraseInput {α : Type} [DecidableEq α] (i j : α) : Product α :=
  if i=j then none else some [j]

theorem eval_eraseInput {α : Type} [DecidableEq α] (t : Net α) (i : α)
    (v : α → Bool) (off : v i = false) :
    (specialize (eraseInput i) t).eval v = t.eval v := by
  rw [eval_specialize]
  congr 1
  funext j
  by_cases h : i=j
  · subst j
    simp [eraseInput,pval,off]
  · simp [eraseInput,pval,h]

/-- Delete all variables in D. Each deletion saves an OR when one surviving
positive input avoids the variable and a surviving pair distinguishes it. -/
theorem restrict_sensitive {α : Type} [DecidableEq α] (t : Net α) (D : Finset α)
    (positive : ∃ w, (∀ i ∈ D, w i = false) ∧ t.eval w = true)
    (flips : ∀ i ∈ D, ∃ x y, (∀ j, j ≠ i → x j = y j) ∧
      (∀ j ∈ D, j ≠ i → x j = false) ∧ t.eval x ≠ t.eval y) :
    ∃ u : Net α, u.cost + D.card ≤ t.cost ∧
      ∀ v, (∀ j ∈ D, v j = false) → u.eval v = t.eval v := by
  classical
  induction D using Finset.induction_on with
  | empty => exact ⟨t,by simp,fun _ _ => rfl⟩
  | @insert i D hi ih =>
    obtain ⟨w,wo,wy⟩ := positive
    have mem (j : α) (hj : j ∈ D) : j ∈ insert i D := Finset.mem_insert_of_mem hj
    obtain ⟨u,lower,keep⟩ := ih ⟨w,fun j hj => wo j (mem j hj),wy⟩ (by
      intro j hj
      obtain ⟨x,y,hxy,hzero,ne⟩ := flips j (mem j hj)
      exact ⟨x,y,hxy,fun k hk => hzero k (mem k hk),ne⟩)
    obtain ⟨x,y,hxy,hzero,ne⟩ := flips i (Finset.mem_insert_self ..)
    have offx (j : α) (hj : j ∈ D) := hzero j (mem j hj) (fun h => hi (h ▸ hj))
    have offy (j : α) (hj : j ∈ D) : y j = false := by
      rw [← hxy j (fun h => hi (h ▸ hj))]
      exact offx j hj
    have used : 0 < hits i u := by
      by_contra! h
      have noOut : ¬outUses i u := by
        intro ou
        have e := outZeros u i ou w (wo i (Finset.mem_insert_self ..))
        rw [keep w (fun j hj => wo j (mem j hj)),wy] at e
        contradiction
      apply ne
      rw [←keep x offx,←keep y offy]
      apply eval_congr_used
      intro j used
      by_cases eq : j=i
      · subst j
        rcases used with us | us
        · omega
        · exact (noOut us).elim
      · exact hxy j eq
    have save := specialize_saves i (eraseInput i) (by simp [eraseInput]) u
    refine ⟨specialize (eraseInput i) u,?_,?_⟩
    · rw [Finset.card_insert_of_notMem hi]
      omega
    · intro v hv
      rw [eval_eraseInput u i v (hv _ (Finset.mem_insert_self ..))]
      exact keep v (fun j hj => hv j (mem j hj))

end FreeAndNet

namespace CrownMixed.Naming
open FreeAndNet
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]

private theorem outside_small (A : Finset I) (h : A.card < Fintype.card I) : ∃ i, i ∉ A := by
  by_contra! no
  have eq : A = Finset.univ := Finset.eq_univ_of_forall no
  rw [eq, Finset.card_univ] at h
  omega

theorem positive_avoiding (N : Naming I α) (n : 3 ≤ Fintype.card I) (x : α) :
    ∃ i j, i≠j ∧ N.val i j x = false := by
  let badR := Finset.univ.filter (fun i => x = N.row i)
  let badC := Finset.univ.filter (fun i => x = N.col i)
  have smallR : badR.card ≤ 1 := Finset.card_le_one.mpr (fun _ h _ k =>
    N.row_inj ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2))
  have smallC : badC.card ≤ 1 := Finset.card_le_one.mpr (fun _ h _ k =>
    N.col_inj ((Finset.mem_filter.mp h).2.symm.trans (Finset.mem_filter.mp k).2))
  obtain ⟨i,hi⟩ := outside_small badR (by omega)
  have cap := Finset.card_insert_le i badC
  obtain ⟨j,hj⟩ := outside_small (insert i badC) (by omega)
  have nri : x ≠ N.row i := fun e => hi (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩)
  have ncj : x ≠ N.col j := fun e => hj (Finset.mem_insert_of_mem (Finset.mem_filter.mpr ⟨Finset.mem_univ _,e⟩))
  exact ⟨i,j,fun e => hj (by simp [e]),by simp [val,nri,ncj]⟩

theorem no_terminal (N : Naming I α) (n : 3 ≤ Fintype.card I) (p : Product α) :
    ¬ N.Rep (.out p) := by
  intro rep
  have ih : Nonempty I := Fintype.card_pos_iff.mp (by omega)
  let i : I := Classical.choice ih
  cases p with
  | none =>
    obtain ⟨j,hj⟩ := outside_small ({i} : Finset I) (by simp; omega)
    have ne : i ≠ j := fun e => hj (by simp [e])
    have h := rep i j
    simp [Net.eval,pval,ne] at h
  | some l =>
    cases l with
    | nil =>
      have h := rep i i
      simp [Net.eval,pval] at h
    | cons x xs =>
      obtain ⟨u,v,ne,off⟩ := positive_avoiding N n x
      have h := rep u v
      simp [Net.eval,pval,off,ne] at h

omit [Fintype I] in
theorem remove_inactive (N : Naming I α) (a b : List α) (tail : Net (Option α))
    (rep : N.Rep (.gate a b tail)) (x : α) (hx : x ∈ a++b)
    (inactive : ¬ ∃ i, N.row i=x ∨ N.col i=x) :
    ∃ u : Net α, N.Rep u ∧ u.cost < (Net.gate a b tail).cost := by
  let t := Net.gate a b tail
  have hit : 0 < hits x t := by
    have mem := List.mem_append.mp hx
    simp [t,hits,mem]
  have save := specialize_saves x (eraseInput x) (by simp [eraseInput]) t
  refine ⟨specialize (eraseInput x) t,?_,by change (specialize (eraseInput x) t).cost < t.cost; omega⟩
  intro i j
  rw [eval_eraseInput]
  · exact rep i j
  · have hr : x ≠ N.row i := fun e => inactive ⟨i,Or.inl e.symm⟩
    have hc : x ≠ N.col j := fun e => inactive ⟨j,Or.inr e.symm⟩
    simp [val,hr,hc]

end CrownMixed.Naming

namespace CrownMixed
open FreeAndNet

abbrev BaseCase := ∀ {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
  (N : Naming I α) (t : Net α), Fintype.card I = 2 → N.Rep t →
  3 * Fintype.card I ≤ t.cost + N.pairs + 5

abbrev GateHitCase := ∀ {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α), N.Rep t → 3 ≤ Fintype.card I →
    t.cost + N.pairs + 5 < 3 * Fintype.card I →
    (∀ i (u : Net α), (N.remove i).Rep u →
      3 * (Fintype.card I - 1) ≤ u.cost + (N.remove i).pairs + 5) →
    ∀ i, hits (N.row i) t ≤ 1 ∧ hits (N.col i) t ≤ 1

abbrev PairStepCase := ∀ {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (a b : List α) (t : Net (Option α)), 3 ≤ Fintype.card I →
    N.Rep (.gate a b t) → 2 ≤ (a.toFinset ∪ b.toFinset).card → a ≠ [] → b ≠ [] →
    (∀ x ∈ a++b, ∃ i, N.row i=x ∨ N.col i=x) →
    (∀ i, hits (N.row i) (.gate a b t) ≤ 1 ∧ hits (N.col i) (.gate a b t) ≤ 1) →
    ∃ M : Naming I (Option α), M.Rep t ∧ M.pairs = N.pairs + 1

private def Case (n k : Nat) := ∀ (I α : Type) [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α), Fintype.card I=n → t.cost=k → 2 ≤ n →
      N.Rep t → 3*n ≤ k+N.pairs+ 5

theorem induct_crown (base : BaseCase) (one : GateHitCase) (pairStep : PairStepCase)
    {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (hn : 2 ≤ Fintype.card I) (rep : N.Rep t) :
    3 * Fintype.card I ≤ t.cost + N.pairs + 5 := by
  have main (n : Nat) : ∀ k, Case n k := by
    induction n using Nat.strong_induction_on with
    | ind n outer =>
      intro k
      induction k using Nat.strong_induction_on with
      | ind k inner =>
        intro I α _ _ _ N t nc kc hn rep
        by_cases three : n=2
        · simpa only [nc,kc] using base N t (nc.trans three) rep
        have large : 3 ≤ Fintype.card I := by omega
        by_contra! bad
        have sameSize (u : Net α) (r : N.Rep u) (small : u.cost < t.cost) : False := by
          have lower := inner u.cost (by omega) I α N u nc rfl hn r
          omega
        cases t with
        | out p => exact (N.no_terminal (by omega) p) rep
        | gate a b t =>
          by_cases deg : a=[] ∨ b=[] ∨ (a.toFinset ∪ b.toFinset).card ≤ 1
          · obtain ⟨u,keep,save⟩ := delete_degenerate_first a b t deg
            exact sameSize u (fun i j => (keep _).trans (rep i j)) save
          by_cases live : ∀ x ∈ a++b, ∃ i, N.row i=x ∨ N.col i=x
          · have hc : (Net.gate a b t).cost + N.pairs + 5 < 3 * Fintype.card I := by omega
            have oneHit := one N (.gate a b t) rep large hc (by
              intro i u ru
              have card : Fintype.card {j : I // j≠i} = n-1 := by
                rw [Fintype.card_subtype_compl (p:=fun j => j=i),Fintype.card_subtype_eq,nc]
              have h := outer (n-1) (by omega) u.cost _ α (N.remove i) u card rfl (by omega) ru
              simpa only [nc] using h)
            obtain ⟨M,mr,mp⟩ := pairStep N a b t large rep (by omega) (fun e=>deg (.inl e))
              (fun e=>deg (.inr (.inl e))) live oneHit
            change t.cost+1=k at kc
            have h := inner t.cost (by omega) I (Option α) M t nc rfl hn mr
            omega
          · push Not at live
            obtain ⟨x,hx,absent⟩ := live
            have inactive : ¬∃ i, N.row i=x ∨ N.col i=x := by
              rintro ⟨i,hi⟩
              rcases hi with h|h <;> simp_all
            obtain ⟨u,ur,sm⟩ := N.remove_inactive a b t rep x hx inactive
            exact sameSize u ur sm
  exact main _ _ I α N t rfl rfl hn rep

end CrownMixed

namespace FreeAndNet
theorem sensitive_has_hit {α : Type} [DecidableEq α] (t : Net α) (b : α)
    (positive : ∃ w : α → Bool, w b = false ∧ t.eval w = true)
    (flip : ∃ x y : α → Bool, (∀ j, j ≠ b → x j = y j) ∧ t.eval x ≠ t.eval y) :
    0 < hits b t := by
  obtain ⟨w,off,yes⟩ := positive
  obtain ⟨x,y,agree,ne⟩ := flip
  by_contra! h
  apply ne
  apply eval_congr_used
  intro j used
  by_cases same : j=b
  · subst j
    rcases used with hit | out
    · omega
    · have zero := outZeros t b out w off
      simp_all
  · exact agree j same

theorem erase_two_saves_hits {α : Type} [DecidableEq α] (t : Net α) (a b : α)
    (positive : ∃ w : α → Bool, w a = false ∧ w b = false ∧ t.eval w = true)
    (flip : ∃ x y : α → Bool, x a = false ∧ y a = false ∧
      (∀ j, j ≠ b → x j = y j) ∧ t.eval x ≠ t.eval y) :
    ∃ u : Net α, u.cost + hits a t + 1 ≤ t.cost ∧
      ∀ v, v a = false → v b = false → u.eval v = t.eval v := by
  let s := specialize (eraseInput a) t
  have keep (v : α → Bool) (off : v a = false) : s.eval v = t.eval v :=
    eval_eraseInput t a v off
  have active : 0 < hits b s := by
    apply sensitive_has_hit
    · obtain ⟨w,offa,offb,yes⟩ := positive
      exact ⟨w,offb,(keep w offa).trans yes⟩
    · obtain ⟨x,y,offx,offy,eq,ne⟩ := flip
      exact ⟨x,y,eq,by rwa [keep x offx,keep y offy]⟩
  have first : s.cost + hits a t ≤ t.cost := specialize_saves a (eraseInput a) (by simp [eraseInput]) t
  have second := specialize_saves b (eraseInput b) (by simp [eraseInput]) s
  refine ⟨specialize (eraseInput b) s, by omega,?_⟩
  intro v va vb
  exact (eval_eraseInput s b v vb).trans (keep v va)
end FreeAndNet

namespace CrownMixed.Naming
open FreeAndNet
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]

theorem pairs_remove (N : Naming I α) (i : I) :
    (N.remove i).pairs + (if N.row i = N.col i then 1 else 0) = N.pairs := by
  classical
  let P := Finset.univ.filter (fun j : I => N.row j = N.col j)
  let T := Finset.univ.filter (fun j : {j : I // j ≠ i} => N.row j.val = N.col j.val)
  let e : {j : I // j ≠ i} ↪ I := Function.Embedding.subtype _
  have eq : T.map e = P.erase i := by
    ext a
    constructor
    · intro h
      obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp h
      exact Finset.mem_erase.mpr ⟨q.property,by simpa [T,P,e] using hq⟩
    · intro h
      obtain ⟨ne,ok⟩ := Finset.mem_erase.mp h
      exact Finset.mem_map.mpr ⟨⟨a,ne⟩,by simpa [T,P] using ok,rfl⟩
  have card : T.card = (P.erase i).card := by simpa using congrArg Finset.card eq
  change T.card + _ = P.card
  rw [card]
  by_cases ok : N.row i = N.col i
  · rw [ite_eq_left ok]
    exact Finset.card_erase_add_one (by simp [P,ok])
  · simp [ite_eq_right ok,Finset.erase_eq_of_notMem (show i ∉ P by simp [P,ok])]

omit [Fintype I] [DecidableEq I] in
private theorem row_off (N : Naming I α) {i j k : I} (hij : i ≠ j) (hik : i ≠ k) :
    N.val j k (N.row i) = false := by
  have a : N.row i ≠ N.row j := fun e => hij (N.row_inj e)
  have b : N.row i ≠ N.col k := fun e => hik (N.same e)
  simp [Naming.val,a,b]

omit [Fintype I] [DecidableEq I] in
private theorem col_off (N : Naming I α) {i j k : I} (hij : i ≠ j) (hik : i ≠ k) :
    N.val j k (N.col i) = false := by
  have a : N.col i ≠ N.row j := fun e => hij (N.same e.symm).symm
  have b : N.col i ≠ N.col k := fun e => hik (N.col_inj e)
  simp [Naming.val,a,b]

private theorem others (i : I) (hn : 3 ≤ Fintype.card I) : ∃ j k : I, i ≠ j ∧ i ≠ k ∧ j ≠ k := by
  classical
  have ex : ∃ j : I, i ≠ j := by
    by_contra! no
    have sub : (Finset.univ : Finset I) ⊆ {i} := fun x _ => by simp [(no x).symm]
    have bound := Finset.card_le_card sub
    simp at bound
    omega
  obtain ⟨j,ij⟩ := ex
  by_contra! no
  have sub : (Finset.univ : Finset I) ⊆ {i,j} := by
    intro x _
    by_cases hx : i=x
    · simp [hx]
    · simp [no j x ij hx]
  have bound := Finset.card_le_card sub
  simp [ij] at bound
  omega

omit [Fintype I] in
private theorem retained (N : Naming I α) (t u : Net α) (i : I) (rep : N.Rep t)
    (keep : ∀ v, v (N.row i) = false → v (N.col i) = false → u.eval v = t.eval v) :
    (N.remove i).Rep u := by
  intro j k
  change u.eval (N.val j.val k.val) = _
  have a := row_off N j.property.symm k.property.symm
  have b := col_off N j.property.symm k.property.symm
  rw [keep _ a b,rep]
  simp only [ne_eq,Subtype.ext_iff]
private theorem all_mono_MixedOneHit {α : Type} (l : List α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : l.all u = true → l.all v = true :=
  fun x => List.all_eq_true.mpr (fun i hi => h i (List.all_eq_true.mp x i hi))

private theorem net_mono_MixedOneHit {α : Type} (t : Net α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : t.eval u = true → t.eval v = true := by
  induction t with
  | out p =>
    cases p with
    | none => simp [Net.eval,pval]
    | some l => exact all_mono_MixedOneHit l u v h
  | gate a b t ih =>
    apply ih
    intro z
    cases z with
    | some i => exact h i
    | none =>
      change a.all u || b.all u = true → a.all v || b.all v = true
      intro e
      rcases Bool.or_eq_true_iff.mp e with hh|hh
      · exact Bool.or_eq_true_iff.mpr (.inl (all_mono_MixedOneHit a _ _ h hh))
      · exact Bool.or_eq_true_iff.mpr (.inr (all_mono_MixedOneHit b _ _ h hh))


omit [Fintype I] in
private theorem singleton_no (N : Naming I α) (t : Net α) (rep : N.Rep t)
    (j : I) (wire : α) (atj : wire = N.row j ∨ wire = N.col j) :
    t.eval (fun z => decide (z=wire)) = false := by
  have no : t.eval (N.val j j) = false := by simpa using rep j j
  cases v : t.eval (fun z => decide (z=wire)) with
  | false => rfl
  | true =>
    have a := net_mono_MixedOneHit t (fun z => decide (z=wire)) (N.val j j) (by
      intro z h
      have eq : z=wire := of_decide_eq_true h
      subst z
      simpa [Naming.val] using atj) v
    simp_all

theorem oneHit (N : Naming I α) (t : Net α) (rep : N.Rep t)
    (hn : 3 ≤ Fintype.card I) (cheap : t.cost + N.pairs + 5 < 3 * Fintype.card I)
    (ih : ∀ i (u : Net α), (N.remove i).Rep u →
      3 * (Fintype.card I - 1) ≤ u.cost + (N.remove i).pairs + 5) :
    ∀ i, hits (N.row i) t ≤ 1 ∧ hits (N.col i) t ≤ 1 := by
  intro i
  have pp := N.pairs_remove i
  by_cases pair : N.row i = N.col i
  · let u := specialize (eraseInput (N.row i)) t
    have save : u.cost + hits (N.row i) t ≤ t.cost :=
      specialize_saves _ (eraseInput (N.row i)) (by simp [eraseInput]) t
    have ur : (N.remove i).Rep u := retained N t u i rep (fun v va _ =>
      eval_eraseInput t _ v va)
    have low := ih i u ur
    rw [ite_eq_left pair] at pp
    have hit : hits (N.row i) t ≤ 1 := by omega
    exact ⟨hit,pair ▸ hit⟩
  · rw [ite_eq_right pair] at pp
    obtain ⟨j,k,ij,ik,jk⟩ := others i hn
    have good : t.eval (N.val j k) = true := by simpa [jk] using rep j k
    have rowj : N.row i ≠ N.row j := fun e => ij (N.row_inj e)
    have colj : N.col i ≠ N.col j := fun e => ij (N.col_inj e)
    have rjfalse := singleton_no N t rep j (N.row j) (Or.inl rfl)
    have cjfalse := singleton_no N t rep j (N.col j) (Or.inr rfl)
    have cjtrue : t.eval (N.val i j) = true := by simpa [ij] using rep i j
    have rjtrue : t.eval (N.val j i) = true := by simpa [ij.symm] using rep j i
    constructor
    · obtain ⟨u,save,keep⟩ := erase_two_saves_hits t (N.row i) (N.col i)
        ⟨N.val j k,row_off N ij ik,col_off N ij ik,good⟩
        ⟨(fun z => decide (z=N.row j)),N.val j i,by simp [rowj],
          by simp [Naming.val,rowj,pair],
          (fun z ne => by simp [Naming.val,ne]),
          by rw [rjfalse,rjtrue]; decide⟩
      have low := ih i u (retained N t u i rep keep)
      omega
    · obtain ⟨u,save,keep⟩ := erase_two_saves_hits t (N.col i) (N.row i)
        ⟨N.val j k,col_off N ij ik,row_off N ij ik,good⟩
        ⟨(fun z => decide (z=N.col j)),N.val i j,by simp [colj],
          by simp [Naming.val,colj,Ne.symm pair],
          (fun z ne => by simp [Naming.val,ne]),
          by rw [cjfalse,cjtrue]; decide⟩
      have low := ih i u (retained N t u i rep (fun v a b => keep v b a))
      omega

end CrownMixed.Naming

namespace CrownMixed.Naming
open FreeAndNet

theorem baseTwo {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (two : Fintype.card I = 2) (rep : N.Rep t) :
    3*Fintype.card I ≤ t.cost+N.pairs+5 := by
  classical
  by_contra! h
  have pz : N.pairs = 0 := by omega
  have zero : t.cost = 0 := by omega
  have apart (i : I) : N.row i ≠ N.col i := by
    intro eq
    have mem : i ∈ Finset.univ.filter (fun j => N.row j=N.col j) := by simp [eq]
    have nonzero : 0 < N.pairs := Finset.card_pos.mpr ⟨i,mem⟩
    omega
  let e := Fintype.equivFinOfCardEq two
  let i := e.symm 0
  let j := e.symm 1
  have ij : i ≠ j := by
    intro same
    have ne : (0 : Fin 2) ≠ 1 := by decide
    exact ne (e.symm.injective same)
  cases t with
  | gate a b u => simp [Net.cost] at zero
  | out p =>
    have ab := rep i j
    have ba := rep j i
    have aa := rep i i
    cases p with
    | none => simp [Net.eval,pval,ij] at ab
    | some l =>
      cases l with
      | nil => simp [Net.eval,pval] at aa
      | cons x xs =>
        have ha : N.val i j x = true := (Bool.and_eq_true_iff.mp
          (show N.val i j x && xs.all (N.val i j) = true by simpa [Net.eval,pval,ij] using ab)).1
        have hb : N.val j i x = true := (Bool.and_eq_true_iff.mp
          (show N.val j i x && xs.all (N.val j i) = true by simpa [Net.eval,pval,Ne.symm ij] using ba)).1
        have ea : x=N.row i ∨ x=N.col j := by simpa [val] using ha
        have eb : x=N.row j ∨ x=N.col i := by simpa [val] using hb
        rcases ea with a|a <;> rcases eb with b|b
        · exact ij (N.row_inj (a.symm.trans b))
        · exact apart i (a.symm.trans b)
        · exact apart j (b.symm.trans a)
        · exact ij (N.col_inj (b.symm.trans a))

end CrownMixed.Naming

namespace CrownMixed
open FreeAndNet
def IsName {I α : Type} (N : Naming I α) (i : I) (x : α) : Prop :=
  N.row i = x ∨ N.col i = x
theorem name_separate {I α : Type} (N : Naming I α) {i j : I} {x y : α}
    (hx : IsName N i x) (hy : IsName N j y) (hne : i ≠ j) : x ≠ y := by
  rintro rfl
  rcases hx with h|h <;> rcases hy with k|k
  · exact hne (N.row_inj (h.trans k.symm))
  · exact hne (N.same (h.trans k.symm))
  · exact hne (N.same (k.trans h.symm)).symm
  · exact hne (N.col_inj (h.trans k.symm))
theorem outside_two {I : Type} [Fintype I] [DecidableEq I]
    (size : 3 ≤ Fintype.card I) (i j : I) : ∃ k, k ≠ i ∧ k ≠ j := by
  classical
  by_contra! h
  have sub : (Finset.univ : Finset I) ⊆ {i,j} := by
    intro k _
    by_cases hi : k=i
    · simp [hi]
    · simp [h k hi]
  have ub := Finset.card_le_card sub
  have bound : ({i,j} : Finset I).card ≤ 2 := by
    simpa using Finset.card_insert_le i ({j} : Finset I)
  simp only [Finset.card_univ] at ub
  omega
private theorem all_mono_MixedPivot {α : Type} (l : List α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : l.all u = true → l.all v = true :=
  fun x => List.all_eq_true.mpr (fun i hi => h i (List.all_eq_true.mp x i hi))

private theorem net_mono_MixedPivot {α : Type} (t : Net α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : t.eval u = true → t.eval v = true := by
  induction t with
  | out p =>
    cases p with
    | none => simp [Net.eval,pval]
    | some l => exact all_mono_MixedPivot l u v h
  | gate a b t ih =>
    apply ih
    intro z
    cases z with
    | some i => exact h i
    | none =>
      change a.all u || b.all u = true → a.all v || b.all v = true
      intro e
      rcases Bool.or_eq_true_iff.mp e with hh|hh
      · exact Bool.or_eq_true_iff.mpr (.inl (all_mono_MixedPivot a _ _ h hh))
      · exact Bool.or_eq_true_iff.mpr (.inr (all_mono_MixedPivot b _ _ h hh))

theorem singleton_cold {I α : Type} [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (rep : N.Rep t) {i : I} {x : α} (hx : IsName N i x) :
    t.eval (fun q => decide (q=x)) = false := by
  cases he : t.eval (fun q => decide (q=x)) with
  | false => rfl
  | true =>
    have hot := net_mono_MixedPivot t _ (N.val i i) (fun j hj => by
      simp only [decide_eq_true_eq] at hj
      subst j
      rcases hx with h|h <;> simp [Naming.val,← h]) he
    simp [rep i i] at hot

theorem mixed_pivot {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (rep : N.Rep t) (size : 3 ≤ Fintype.card I)
    {i j : I} {x y : α} (hx : IsName N i x) (hy : IsName N j y) :
    ∃ v w : α → Bool, v y = false ∧ (∀ q, q ≠ x → v q = w q) ∧ t.eval v ≠ t.eval w := by
  obtain ⟨k,ki,kj⟩ := outside_two size i j
  rcases hx with rfl|rfl
  · have off := name_separate N (.inr (rfl : N.col k = _)) hy kj
    refine ⟨fun q => decide (q=N.col k), N.val i k, by simp [Ne.symm off], ?_, ?_⟩
    · intro q hq; simp [Naming.val,hq]
    · rw [singleton_cold N t rep (.inr (rfl : N.col k = _)), rep]
      simp [Ne.symm ki]
  · have off := name_separate N (.inl (rfl : N.row k = _)) hy kj
    refine ⟨fun q => decide (q=N.row k), N.val k i, by simp [Ne.symm off], ?_, ?_⟩
    · intro q hq; simp [Naming.val,hq]
    · rw [singleton_cold N t rep (.inl (rfl : N.row k = _)), rep]
      simp [ki]
theorem named_no_output {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (rep : N.Rep t) (size : 3 ≤ Fintype.card I)
    {i : I} {x : α} (hx : IsName N i x) : ¬outUses x t := by
  obtain ⟨j,ji,_⟩ := outside_two size i i
  obtain ⟨k,ki,kj⟩ := outside_two size i j
  intro used
  have off₁ := name_separate N hx (.inl (rfl : N.row j = _)) ji.symm
  have off₂ := name_separate N hx (.inr (rfl : N.col k = _)) ki.symm
  have cold := outZeros t x used (N.val j k) (by simp [Naming.val,off₁,off₂])
  simp [rep j k,kj.symm] at cold
end CrownMixed

namespace ParentCrown
open FreeAndNet

private theorem pin_congr {α : Type} (l : List α) {v w : α → Bool}
    (h : ∀ j ∈ l, v j = w j) : l.all v = l.all w := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    simp only [List.all_cons, h x (by simp), ih (fun j hj => h j (by simp [hj]))]

private theorem pin_off {α : Type} {l : List α} {v : α → Bool} {j : α}
    (mem : j ∈ l) (off : v j = false) : l.all v = false := by
  cases he : l.all v with
  | false => rfl
  | true => have hh := List.all_eq_true.mp he j mem; simp_all

/-- A change to one atom read only at this gate cannot affect the output
if the output of the gate stays the same. -/
theorem first_gate_externality {α : Type} [DecidableEq α] {a b : List α}
    {t : Net (Option α)} {x : α} (fresh : hits (some x) t = 0 ∧ ¬outUses (some x) t)
    {v w : α → Bool} (eqOther : ∀ j, j ≠ x → v j = w j)
    (gateEq : (a.all v || b.all v) = (a.all w || b.all w)) :
    (Net.gate a b t).eval v = (Net.gate a b t).eval w := by
  simp only [Net.eval]
  apply eval_congr_used
  intro j hj
  cases j with
  | none => exact gateEq
  | some i =>
    by_cases hi : i = x
    · subst i
      rcases hj with h | h
      · omega
      · exact (fresh.2 h).elim
    · exact eqOther i hi

/-- On each pin every occurrence names the same atom. Repeated factors are
permitted. A pivot for x can be exhibited with any other y fixed false. -/
theorem first_gate_pin_unique {α : Type} [DecidableEq α] (a b : List α)
    (t : Net (Option α))
    (fresh : ∀ x, x ∈ a ∨ x ∈ b → hits (some x) t = 0 ∧ ¬outUses (some x) t)
    (pivot : ∀ x y : α, (x ∈ a ∨ x ∈ b) → (y ∈ a ∨ y ∈ b) → x ≠ y → ∃ v w : α → Bool,
      v y = false ∧ (∀ j, j ≠ x → v j = w j) ∧
      (Net.gate a b t).eval v ≠ (Net.gate a b t).eval w) :
    (∀ x ∈ a, ∀ y ∈ a, x = y) ∧ (∀ x ∈ b, ∀ y ∈ b, x = y) := by
  have force (l m : List α) (x y : α) (xy : x ≠ y) (xl : x ∈ l) (yl : y ∈ l)
      (freshX : hits (some x) t = 0 ∧ ¬outUses (some x) t)
      (freshY : hits (some y) t = 0 ∧ ¬outUses (some y) t)
      (xpin : x ∈ a ∨ x ∈ b) (ypin : y ∈ a ∨ y ∈ b)
      (equiv : ∀ v : α → Bool, (a.all v || b.all v) = (l.all v || m.all v)) : False := by
    by_cases xm : x ∈ m
    · obtain ⟨v,w,off,eqo,dist⟩ := pivot y x ypin xpin xy.symm
      have off' : w x = false := (eqo x xy).symm.trans off
      apply dist
      apply first_gate_externality freshY eqo
      rw [equiv v, equiv w, pin_off xl off, pin_off xl off', pin_off xm off, pin_off xm off']
    · obtain ⟨v,w,off,eqo,dist⟩ := pivot x y xpin ypin xy
      have off' : w y = false := (eqo y xy.symm).symm.trans off
      apply dist
      apply first_gate_externality freshX eqo
      rw [equiv v, equiv w, pin_off yl off, pin_off yl off']
      exact congrArg (fun q => false || q) (pin_congr m (fun j hj => eqo j (fun h => xm (h ▸ hj))))
  constructor
  · intro x hx y hy
    by_contra xy
    exact force a b x y xy hx hy (fresh x (.inl hx)) (fresh y (.inl hy)) (.inl hx) (.inl hy) (fun _ => rfl)
  · intro x hx y hy
    by_contra xy
    exact force b a x y xy hx hy (fresh x (.inr hx)) (fresh y (.inr hy)) (.inr hx) (.inr hy) (fun _ => Bool.or_comm ..)

end ParentCrown

namespace CrownMixed.Naming
open FreeAndNet
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
theorem firstShape (N : Naming I α) (hn : 3 ≤ Fintype.card I) (a b : List α)
    (t : Net (Option α)) (rep : N.Rep (.gate a b t))
    (live : ∀ x ∈ a++b, ∃ i, N.row i=x ∨ N.col i=x)
    (one : ∀ i, hits (N.row i) (.gate a b t) ≤ 1 ∧ hits (N.col i) (.gate a b t) ≤ 1) :
    (∀ x ∈ a, ∀ y ∈ a, x=y) ∧ (∀ x ∈ b, ∀ y ∈ b, x=y) ∧
    ∀ x ∈ a++b, hits (some x) t=0 ∧ ¬outUses (some x) t := by
  have fresh (x : α) (mem : x ∈ a ∨ x ∈ b) :
      hits (some x) t=0 ∧ ¬outUses (some x) t := by
    obtain ⟨i,hi⟩ := live x (List.mem_append.mpr mem)
    have ub : hits x (.gate a b t) ≤ 1 := by
      rcases hi with rfl|rfl
      · exact (one i).1
      · exact (one i).2
    simp [hits,mem] at ub
    exact ⟨by omega, named_no_output N (.gate a b t) rep (by omega) hi⟩
  obtain ⟨pa,pb⟩ := ParentCrown.first_gate_pin_unique a b t fresh (by
    intro x y hx hy _
    obtain ⟨i,hi⟩ := live x (List.mem_append.mpr hx)
    obtain ⟨j,hj⟩ := live y (List.mem_append.mpr hy)
    exact mixed_pivot N _ rep (by omega) hi hj)
  exact ⟨pa,pb,fun x hx => fresh x (List.mem_append.mp hx)⟩

omit [DecidableEq α] in
theorem pin_all_eq {l : List α} {x : α} (hx : x ∈ l)
    (unique : ∀ j ∈ l, j=x) (v : α → Bool) : l.all v = v x := by
  apply Bool.eq_iff_iff.mpr
  exact ⟨fun h => List.all_eq_true.mp h x hx,
    fun h => List.all_eq_true.mpr (fun j hj => (unique j hj).symm ▸ h)⟩
theorem pair_externality (a b : List α) (t : Net (Option α)) (x y : α)
    (gate : ∀ v, (a.all v || b.all v) = (v x || v y))
    (fx : hits (some x) t=0 ∧ ¬outUses (some x) t)
    (fy : hits (some y) t=0 ∧ ¬outUses (some y) t)
    (v w : α → Bool) (agree : ∀ j, j≠x → j≠y → v j=w j)
    (same : (v x || v y)=(w x || w y)) :
    (Net.gate a b t).eval v = (Net.gate a b t).eval w := by
  simp only [Net.eval]
  apply eval_congr_used
  intro j used
  cases j with
  | none => exact (gate v).trans (same.trans (gate w).symm)
  | some j =>
    by_cases jx : j=x
    · subst j
      rcases used with h|h
      · omega
      · exact (fx.2 h).elim
    by_cases jy : j=y
    · subst j
      rcases used with h|h
      · omega
      · exact (fy.2 h).elim
    exact agree j jx jy
end CrownMixed.Naming

namespace CrownMixed.Naming
open FreeAndNet
private theorem all_mono_MixedClassification {α : Type} (l : List α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : l.all u = true → l.all v = true :=
  fun x => List.all_eq_true.mpr (fun i hi => h i (List.all_eq_true.mp x i hi))

private theorem net_mono_MixedClassification {α : Type} (t : Net α) (u v : α → Bool)
    (h : ∀ i, u i = true → v i = true) : t.eval u = true → t.eval v = true := by
  induction t with
  | out p =>
    cases p with
    | none => simp [Net.eval,pval]
    | some l => exact all_mono_MixedClassification l u v h
  | gate a b t ih =>
    apply ih
    intro z
    cases z with
    | some i => exact h i
    | none =>
      change a.all u || b.all u = true → a.all v || b.all v = true
      intro e
      rcases Bool.or_eq_true_iff.mp e with hh|hh
      · exact Bool.or_eq_true_iff.mpr (.inl (all_mono_MixedClassification a _ _ h hh))
      · exact Bool.or_eq_true_iff.mpr (.inr (all_mono_MixedClassification b _ _ h hh))


/-- If two distinct named atoms are seen only through their disjunction,
they must be the two endpoints of a single label. -/
theorem matched_of_external {I α : Type} [DecidableEq α] [DecidableEq I]
    (N : Naming I α) (t : Net α) (rep : N.Rep t) (x y : α) (ne : x ≠ y)
    (nx : ∃ i, x = N.row i ∨ x = N.col i) (ny : ∃ i, y = N.row i ∨ y = N.col i)
    (ext : ∀ v w : α → Bool, (∀ z, z ≠ x → z ≠ y → v z = w z) →
      (v x || v y) = (w x || w y) → t.eval v = t.eval w) :
    ∃ i, (x = N.row i ∧ y = N.col i) ∨ (x = N.col i ∧ y = N.row i) := by
  have conflict (i a b : I) (ab : a ≠ b) (hx : x = N.row i ∨ x = N.col i)
      (sub : ∀ z, z = N.row a ∨ z = N.col b →
        z = x ∨ z = y ∨ z = N.row i ∨ z = N.col i) : False := by
    let augmented : α → Bool := fun z => decide (z = x ∨ z = y ∨ z = N.row i ∨ z = N.col i)
    have agree := ext (N.val i i) augmented (by intro z zx zy; simp [augmented,val,zx,zy])
      (by simp [val,augmented,hx])
    have hot : t.eval augmented = true := net_mono_MixedClassification t (N.val a b) augmented
      (fun z h => decide_eq_true (sub z (of_decide_eq_true h))) (by simp [rep a b,ab])
    rw [← agree,rep i i] at hot
    simp at hot
  obtain ⟨i,hx⟩ := nx
  obtain ⟨j,hy⟩ := ny
  by_cases ij : i = j
  · subst j
    exact ⟨i, by rcases hx with h|h <;> rcases hy with z|z <;> simp_all⟩
  · exfalso
    rcases hx with h|h <;> rcases hy with k|k
    · exact conflict i j i (Ne.symm ij) (Or.inl h) (by intro z hs; rw [h,k]; tauto)
    · exact conflict i i j ij (Or.inl h) (by intro z hs; rw [h,k]; tauto)
    · exact conflict i j i (Ne.symm ij) (Or.inr h) (by intro z hs; rw [h,k]; tauto)
    · exact conflict i i j ij (Or.inr h) (by intro z hs; rw [h,k]; tauto)
end CrownMixed.Naming

namespace CrownMixed.Naming
open FreeAndNet
variable {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]

theorem forcedPair (N : Naming I α) (hn : 3 ≤ Fintype.card I) (a b : List α)
    (t : Net (Option α)) (rep : N.Rep (.gate a b t))
    (live : ∀ x ∈ a++b, ∃ i, N.row i=x ∨ N.col i=x)
    (one : ∀ i, hits (N.row i) (.gate a b t) ≤ 1 ∧ hits (N.col i) (.gate a b t) ≤ 1)
    (distinct : ∃ x ∈ a++b, ∃ y ∈ a++b, x≠y) :
    ∃ i, N.row i≠N.col i ∧
      (∀ v, (a.all v || b.all v) = (v (N.row i) || v (N.col i))) ∧
      (hits (some (N.row i)) t=0 ∧ ¬outUses (some (N.row i)) t) ∧
      (hits (some (N.col i)) t=0 ∧ ¬outUses (some (N.col i)) t) := by
  obtain ⟨pa,pb,fresh⟩ := firstShape N hn a b t rep live one
  obtain ⟨q,hq,r,hr,qr⟩ := distinct
  have exa : ∃ x, x ∈ a := by
    by_contra! ha
    exact qr (pb q ((List.mem_append.mp hq).resolve_left (ha q)) r
      ((List.mem_append.mp hr).resolve_left (ha r)))
  have exb : ∃ y, y ∈ b := by
    by_contra! hb
    exact qr (pa q ((List.mem_append.mp hq).resolve_right (hb q)) r
      ((List.mem_append.mp hr).resolve_right (hb r)))
  obtain ⟨x,hx⟩ := exa
  obtain ⟨y,hy⟩ := exb
  have xy : x≠y := by
    intro eq
    have allx (u : α) (hu : u ∈ a++b) : u=x :=
      (List.mem_append.mp hu).elim (fun h => pa u h x hx)
        (fun h => (pb u h y hy).trans eq.symm)
    exact qr ((allx q hq).trans (allx r hr).symm)
  have gate (v : α → Bool) : (a.all v || b.all v)=(v x || v y) := by
    rw [pin_all_eq hx (fun u hu => pa u hu x hx),pin_all_eq hy (fun u hu => pb u hu y hy)]
  have hx' : x ∈ a++b := List.mem_append.mpr (.inl hx)
  have hy' : y ∈ a++b := List.mem_append.mpr (.inr hy)
  have name (z : α) (hz : z ∈ a++b) : ∃ i, z=N.row i ∨ z=N.col i := by
    obtain ⟨i,hi⟩ := live z hz
    exact ⟨i,hi.imp Eq.symm Eq.symm⟩
  obtain ⟨i,e|e⟩ := matched_of_external N _ rep x y xy (name x hx') (name y hy')
    (pair_externality a b t x y gate (fresh x hx') (fresh y hy'))
  · obtain ⟨rfl,rfl⟩ := e
    exact ⟨i,xy,gate,fresh _ hx',fresh _ hy'⟩
  · obtain ⟨rfl,rfl⟩ := e
    exact ⟨i,xy.symm,fun v => (gate v).trans (Bool.or_comm ..),fresh _ hy',fresh _ hx'⟩
end CrownMixed.Naming

namespace CrownMixed.Naming
open FreeAndNet
variable {I α : Type}

private def merged [DecidableEq I] (f : I → α) (i j : I) : Option α :=
  if j=i then none else some (f j)

private theorem merged_eq [DecidableEq I] {f g : I → α} {i j k : I} :
    merged f i j = merged g i k ↔ (j=i ∧ k=i) ∨ (j≠i ∧ k≠i ∧ f j = g k) := by
  by_cases hj : j=i <;> by_cases hk : k=i <;> simp [merged,hj,hk]

def merge [DecidableEq I] (N : Naming I α) (i : I) : Naming I (Option α) where
  row := merged N.row i
  col := merged N.col i
  row_inj := fun _ _ h => (merged_eq.mp h).elim (fun e => e.1.trans e.2.symm) (fun e => N.row_inj e.2.2)
  col_inj := fun _ _ h => (merged_eq.mp h).elim (fun e => e.1.trans e.2.symm) (fun e => N.col_inj e.2.2)
  same := fun h => (merged_eq.mp h).elim (fun e => e.1.trans e.2.symm) (fun e => N.same e.2.2)

theorem merge_pairs [Fintype I] [DecidableEq I] [DecidableEq α] (N : Naming I α) (i : I)
    (h : N.row i ≠ N.col i) : (N.merge i).pairs = N.pairs+1 := by
  let P := Finset.univ.filter (fun j => N.row j = N.col j)
  have e : (Finset.univ.filter (fun j => (N.merge i).row j = (N.merge i).col j)) = insert i P := by
    ext j
    simp only [Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_insert,P,merge,merged_eq]
    by_cases hj : j=i <;> simp [hj]
  have off : i ∉ P := by simp [P,h]
  exact (congrArg Finset.card e).trans (Finset.card_insert_of_notMem off)

theorem followMerge [Fintype I] [DecidableEq I] [DecidableEq α] (N : Naming I α) (i : I)
    {a b : List α} {t : Net (Option α)} (rep : N.Rep (.gate a b t))
    (unpaired : N.row i ≠ N.col i)
    (gate : ∀ v, (a.all v || b.all v) = (v (N.row i) || v (N.col i)))
    (rowFresh : hits (some (N.row i)) t = 0 ∧ ¬outUses (some (N.row i)) t)
    (colFresh : hits (some (N.col i)) t = 0 ∧ ¬outUses (some (N.col i)) t) :
    ∃ M : Naming I (Option α), M.Rep t ∧ M.pairs = N.pairs+1 := by
  refine ⟨N.merge i,?_,merge_pairs N i unpaired⟩
  intro p q
  refine Eq.trans ?_ (rep p q)
  change t.eval _ = t.eval _
  apply eval_congr_used
  intro j used
  cases j with
  | none =>
    change (N.merge i).val p q none = (a.all (N.val p q) || b.all (N.val p q))
    rw [gate]
    apply Bool.eq_iff_iff.mpr
    simp only [val,merge,merged,Bool.or_eq_true_iff,decide_eq_true_eq]
    by_cases hp : p=i <;> by_cases hq : q=i <;> simp [hp,hq];
      first | tauto | grind [N.row_inj.eq_iff,N.col_inj.eq_iff,N.same]
  | some j =>
    have neR : j ≠ N.row i := by
      rintro rfl
      rcases used with h|h
      · omega
      · exact rowFresh.2 h
    have neC : j ≠ N.col i := by
      rintro rfl
      rcases used with h|h
      · omega
      · exact colFresh.2 h
    change (N.merge i).val p q (some j) = N.val p q j
    by_cases hp : p=i <;> by_cases hq : q=i <;> simp [val,merge,merged,hp,hq,neR,neC]

end CrownMixed.Naming

namespace FreeAndNet.CircuitCompiler
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def orFlag (g : Gate) : Bool :=
  match g.op with | .or => true | _ => false

def orStep {α : Type} (w : List (Product α)) (p q : Product α)
    (k : ∀ {β : Type}, List (Product β) → Net β) : Net α :=
  match p,q with
  | none,t | t,none => k (w ++ [t])
  | some a,some b => .gate a b (k (w.map liftP ++ [some [none]]))

def run (out : ℕ) : (gs : List Gate) → {α : Type} → List (Product α) → Net α
  | [], _, w => .out (w.getD out none)
  | g :: gs, _, w =>
    if orFlag g then
      orStep w (w.getD (g.inputs.getD 0 w.length) none)
        (w.getD (g.inputs.getD 1 w.length) none) (run out gs)
    else run out gs (w ++ [substProduct (fun i => w.getD i none) g.inputs])

def concreteStep (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map (fun i => w.getD i false))]

private theorem read_eq {α : Type} (w : List (Product α)) (v : α → Bool) (i : ℕ) :
    pval v (w.getD i none) = (w.map (pval v)).getD i false :=
  (List.getD_map (d := (none : Product α)) (l := w) (n := i) (pval v)).symm

private theorem eval_lift {α : Type} (v : α → Bool) (b : Bool) (p : Product α) :
    pval (fun z : Option α => z.elim b v) (liftP p) = pval v p := by
  cases p <;> simp [pval,liftP,Function.comp_def]

private theorem getD_end {α : Type} (w : List α) (z : α) : w.getD w.length z = z := by
  simp [List.getD_eq_getElem?_getD]

private theorem evalOrInputs (ins : List ℕ) (w : List Bool) (len : ins.length ≤ 2) :
    (w.getD (ins.getD 0 w.length) false || w.getD (ins.getD 1 w.length) false) =
      GateOp.or.eval (ins.map (fun i => w.getD i false)) := by
  cases ins with
  | nil => simp [GateOp.eval]
  | cons a as =>
    cases as with
    | nil => simp [GateOp.eval,List.getD]
    | cons b bs =>
      cases bs with
      | nil => simp [GateOp.eval,List.getD]
      | cons c cs => simp at len

private theorem eval_orStep {α : Type} (w : List (Product α)) (p q : Product α)
    (k : ∀ {β : Type}, List (Product β) → Net β) (v : α → Bool)
    (f : List Bool → Bool)
    (hk : ∀ {β : Type} (w' : List (Product β)) (v' : β → Bool),
      (k w').eval v' = f (w'.map (pval v'))) :
    (orStep w p q k).eval v =
      f (w.map (pval v) ++ [pval v p || pval v q]) := by
  cases p with
  | none => simp [orStep,hk,pval]
  | some a =>
    cases q with
    | none => simp [orStep,hk,pval]
    | some b =>
      simp only [orStep,Net.eval,hk,List.map_append,List.map_cons,List.map_nil,List.map_map]
      congr 2
      · exact List.map_congr_left fun x _ => eval_lift v _ x
      · simp [pval]

private theorem run_eval (out : ℕ) (gs : List Gate)
    (hg : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    {α : Type} (w : List (Product α)) (v : α → Bool) :
    (run out gs w).eval v = (gs.foldl concreteStep (w.map (pval v))).getD out false := by
  induction gs generalizing α with
  | nil => exact read_eq w v out
  | cons g gs ih =>
    have ht := fun g' (h : g' ∈ gs) => hg g' (List.mem_cons_of_mem _ h)
    obtain ⟨hop, hlen⟩ := hg g List.mem_cons_self
    rcases hop with ha | ho
    · simp only [run,orFlag,ha,Bool.false_eq_true,ite_false,ih ht,List.foldl_cons,
        concreteStep,List.map_append,List.map_cons,List.map_nil,pval_subst]
      congr 3
      simp only [GateOp.eval, List.all_map,Function.comp_def,id_eq, read_eq]
    · simp only [run,orFlag,ho,ite_true,List.foldl_cons]
      rw [eval_orStep _ _ _ _ _ (fun z => (gs.foldl concreteStep z).getD out false)
        (fun w' v' => ih ht w' v')]
      simp only [concreteStep,ho,read_eq]
      have hbit := evalOrInputs g.inputs (w.map (pval v)) hlen
      simp only [List.length_map] at hbit
      rw [hbit]

private theorem cost_orStep {α : Type} (w : List (Product α)) (p q : Product α)
    (k : ∀ {β : Type}, List (Product β) → Net β) (n : ℕ)
    (hk : ∀ {β : Type} (w' : List (Product β)), (k w').cost ≤ n) :
    (orStep w p q k).cost ≤ n + 1 := by
  cases p <;> cases q <;> simp only [orStep,Net.cost]
  all_goals first | exact Nat.le.step (hk _) | exact Nat.succ_le_succ (hk _)

theorem run_cost (out : ℕ) (gs : List Gate) {α : Type} (w : List (Product α)) :
    (run out gs w).cost ≤ (gs.filter orFlag).length := by
  induction gs generalizing α with
  | nil => simp [run,Net.cost]
  | cons g gs ih =>
    cases hg : orFlag g
    · simpa [run,hg] using ih (w ++ [substProduct (fun i => w.getD i none) g.inputs])
    · simpa [run,hg] using cost_orStep w (w.getD (g.inputs.getD 0 w.length) none)
        (w.getD (g.inputs.getD 1 w.length) none) (run out gs) (gs.filter orFlag).length ih

def compile (n : ℕ) (C : Circuit) : Net (Fin n) :=
  run C.output C.gates (List.ofFn fun i : Fin n => some [i])

theorem compile_eval (n : ℕ) (C : Circuit) (hm : Monotone2 C) (v : Fin n → Bool) :
    (compile n C).eval v = C.eval (List.ofFn v) := by
  unfold compile
  rw [run_eval _ _ (fun g hg => ⟨(hm g hg).1,(hm g hg).2⟩)]
  change _ = (C.gates.foldl concreteStep (List.ofFn v)).getD C.output false
  congr 2
  simp [pval,List.map_ofFn,Function.comp_def]

theorem compile_cost (n : ℕ) (C : Circuit) :
    (compile n C).cost ≤ (C.gates.filter orFlag).length :=
  run_cost _ _ _

end FreeAndNet.CircuitCompiler

namespace CrownMixed
open FreeAndNet FreeAndNet.CircuitCompiler PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def physicalNaming : Naming (Fin 12) (Fin 24) where
  row i := Fin.castAdd 12 i
  col j := Fin.natAdd 12 j
  row_inj := fun _ _ h => Fin.ext (congrArg (fun x : Fin 24 => x.val) h)
  col_inj := by
    intro i j h
    apply Fin.ext
    have e := congrArg (fun x : Fin 24 => x.val) h
    change 12+i.val=12+j.val at e
    omega
  same := by
    intro i j h
    have e := congrArg (fun x : Fin 24 => x.val) h
    change i.val = 12 + j.val at e
    omega

theorem physicalPair : ∀ i j, List.ofFn (physicalNaming.val i j) = oneEach i j := by decide

theorem from_mixed_lower (M : ∀ {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α), 2 ≤ Fintype.card I → N.Rep t →
    3*Fintype.card I ≤ t.cost+N.pairs+ 5)
    (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i≠j)) C) :
    31 ≤ (C.gates.filter orFlag).length := by
  have hr : physicalNaming.Rep (compile 24 C) := by
    intro i j
    rw [compile_eval _ _ hm,physicalPair]
    exact rep i j
  have lo := M physicalNaming (compile 24 C) (by decide) hr
  have zero : physicalNaming.pairs=0 := by decide
  have cap := compile_cost 24 C
  simp only [Fintype.card_fin,zero] at lo
  omega

end CrownMixed

namespace CrownMixed
open FreeAndNet PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem mixed_or_lower {I α : Type} [Fintype I] [DecidableEq I] [DecidableEq α]
    (N : Naming I α) (t : Net α) (hn : 2 ≤ Fintype.card I) (rep : N.Rep t) :
    3*Fintype.card I ≤ t.cost+N.pairs+ 5 := by
  apply induct_crown (fun N t => N.baseTwo t) (fun N t => N.oneHit t) _ N t hn rep
  intro I α _ _ _ N a b t large rep card _ _ live one
  have distinct : ∃ x ∈ a++b, ∃ y ∈ a++b, x≠y := by
    simpa only [Finset.mem_union,List.mem_toFinset,List.mem_append] using
      Finset.one_lt_card.mp card
  obtain ⟨i,unpaired,gate,rowFresh,colFresh⟩ := N.forcedPair large a b t rep live one distinct
  exact N.followMerge i rep unpaired gate rowFresh colFresh

theorem crown_twelve_requires_thirty_one_ors (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i≠j)) C) :
    31 ≤ (C.gates.filter CircuitCompiler.orFlag).length :=
  from_mixed_lower (fun N t => mixed_or_lower N t) C hm rep

end CrownMixed

namespace CrownMixed
open FreeAndNet FreeAndNet.CircuitCompiler PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

def andFlag (g : Gate) : Bool :=
  match g.op with | .and => true | _ => false

private theorem gate_budget (gs : List Gate) :
    (gs.filter orFlag).length + (gs.filter andFlag).length ≤ gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    cases h : g.op <;> simp [orFlag,andFlag,h] <;> omega

theorem crown_twelve_size_at_least_or_lower_plus_ands (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i≠j)) C) :
    31 + (C.gates.filter andFlag).length ≤ C.size := by
  have lo := crown_twelve_requires_thirty_one_ors C hm rep
  have bound := gate_budget C.gates
  change _ ≤ C.gates.length
  omega

theorem crown_twelve_size_forty_has_at_most_nine_ands (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun i j : Fin 12 => decide (i≠j)) C) (small : C.size ≤ 40) :
    (C.gates.filter andFlag).length ≤ 9 := by
  have := crown_twelve_size_at_least_or_lower_plus_ands C hm rep
  omega
end CrownMixed

#print axioms CrownMixed.crown_twelve_size_forty_has_at_most_nine_ands
