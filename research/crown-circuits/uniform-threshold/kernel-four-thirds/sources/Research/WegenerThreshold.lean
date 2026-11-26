import Research.ThresholdFactors
import Mathlib.Data.Finset.Card
import Mathlib.Data.List.Basic
import Mathlib.Data.Fintype.Card
import PEqualNP.Defs.MetaComplexityLgpMono
import Mathlib.Data.List.GetD

/-!
# OR lower bound for the second threshold function

A fan-in-two monotone circuit computing threshold two requires at least
twice its number of inputs minus four OR gates. This is the lower bound in
Ingo Wegener, *The Complexity of Boolean Functions* (1987), §6.3, Theorem 3.1(ii).

The proof represents intervening AND gates as products of earlier signals.
Unless the first OR is redundant, one primary input occurs in two ORs:
otherwise the union of the first OR's raw inputs reaches the rest of the
computation through one bit. The corresponding restriction removes both ORs.
-/



namespace ThresholdFactors

/-- Three weights on the hidden variables leave three distinguishable residual
functions on the visible variables, which one Boolean signal cannot encode. -/
theorem oneBitCut {α : Type*} [DecidableEq α] (u : Finset α)
    (i j k : α) (ij : i ≠ j) (hi : i ∈ u) (hj : j ∈ u) (hk : k ∉ u)
    (bit : Finset α → Bool) (post : Bool → Finset α → Prop) :
    ¬ ∀ x : Finset α, Two x ↔ post (bit (x ∩ u)) (x \ u) := by
  classical
  intro h
  have ki : k ≠ i := fun e => hk (e ▸ hi)
  have s0 := h ∅
  have s1 := h {i}
  have s2 := h {i,j}
  have t0 := h {k}
  have t1 := h {k,i}
  have e1 : ({i} : Finset α) ∩ u = {i} := Finset.inter_eq_left.mpr (by simpa using hi)
  have d1 : ({i} : Finset α) \ u = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (by simpa using hi)
  have e2 : ({i,j} : Finset α) ∩ u = {i,j} := Finset.inter_eq_left.mpr (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; rcases ht with rfl|rfl <;> assumption)
  have d2 : ({i,j} : Finset α) \ u = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (by intro t ht; simp only [Finset.mem_insert, Finset.mem_singleton] at ht; rcases ht with rfl|rfl <;> assumption)
  have ek : ({k} : Finset α) ∩ u = ∅ := by ext x; simp; aesop
  have dk : ({k} : Finset α) \ u = {k} := by ext x; simp; aesop
  have eti : ({k,i} : Finset α) ∩ u = {i} := by ext x; simp; aesop
  have dti : ({k,i} : Finset α) \ u = {k} := by ext x; simp; aesop
  simp [Two] at s0
  simp [Two, e1,d1] at s1
  simp [Two, e2,d2,ij] at s2
  simp [Two, ek,dk] at t0
  simp [Two,eti,dti,ki] at t1
  cases a : bit ∅ <;> cases b : bit {i} <;> cases c : bit {i,j} <;> simp_all

end ThresholdFactors

namespace ThresholdFactors
/-- At least three monotone conjunctions are necessary even after arbitrary
one-bit postprocessing, on any domain with at least three inputs. -/
theorem twoTermsCut {α : Type*} [DecidableEq α] (i j k : α)
    (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) (a b : Finset α)
    (post : Bool → Prop) :
    ¬ ∀ x : Finset α, Two x ↔ post (decide (a ⊆ x ∨ b ⊆ x)) := by
  classical
  intro repr
  let big := insert i (insert j (insert k (a ∪ b)))
  have hb : Two big := by
    have ss : ({i,j} : Finset α) ⊆ big := by simp [big]
    have hc := Finset.card_le_card ss
    simpa [Two,hij] using hc
  have ha : a ⊆ big := by dsimp [big]; intro t ht; simp [Finset.mem_union_left _ ht]
  have ht : post true := by simpa [ha] using (repr big).mp hb
  have hf : ¬ post false := by
    intro f
    have all (v : Bool) : post v := by cases v <;> assumption
    have e := (repr ∅).mpr (all _)
    simp [Two] at e
  have eq (x : Finset α) : Two x ↔ a ⊆ x ∨ b ⊆ x := by
    by_cases h : a ⊆ x ∨ b ⊆ x <;> simpa [h,ht,hf] using repr x
  have forced (x y : α) (hne : x ≠ y) : a = {x,y} ∨ b = {x,y} := by
    have h := (eq {x,y}).mp (by simp [Two,hne])
    have aux (c : Finset α) (hc : c = a ∨ c = b) (sub : c ⊆ {x,y}) : c = {x,y} := by
      have cc : Two c := (eq c).mpr (by rcases hc with rfl|rfl <;> simp)
      apply Finset.eq_of_subset_of_card_le sub
      simpa [Two,hne] using cc
    exact h.elim (fun s => Or.inl (aux a (Or.inl rfl) s)) (fun s => Or.inr (aux b (Or.inr rfl) s))
  have pij := forced i j hij
  have pik := forced i k hik
  have pjk := forced j k hjk
  have d1 : ({i,j} : Finset α) ≠ {i,k} := fun h => by
    have t : j ∈ ({i,k} : Finset α) := h ▸ (by simp : j ∈ ({i,j} : Finset α))
    simp [Ne.symm hij,hjk] at t
  have d2 : ({i,j} : Finset α) ≠ {j,k} := fun h => by
    have t : i ∈ ({j,k} : Finset α) := h ▸ (by simp : i ∈ ({i,j} : Finset α))
    simp [hij,hik] at t
  have d3 : ({i,k} : Finset α) ≠ {j,k} := fun h => by
    have t : i ∈ ({j,k} : Finset α) := h ▸ (by simp : i ∈ ({i,k} : Finset α))
    simp [hij,hik] at t
  grind
end ThresholdFactors

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

namespace FreeAndNet
open ThresholdFactors

def Computes {α : Type} [DecidableEq α] (t : Net α) : Prop :=
  ∀ x : Finset α, t.eval (fun i => decide (i ∈ x)) = true ↔ Two x

theorem noOutputRaw {α : Type} [Fintype α] [DecidableEq α] (n : 3 ≤ Fintype.card α)
    {t : Net α} (h : Computes t) (i : α) : ¬ outUses i t := by
  intro used
  let x := (Finset.univ : Finset α).erase i
  have c : Two x := by simp [Two,x,Finset.card_erase_of_mem]; omega
  have z := outZeros t i used (fun i => decide (i ∈ x)) (by simp [x])
  rw [(h x).mpr c] at z
  contradiction

theorem gate_cut {α : Type} [DecidableEq α] (a b : List α) (t : Net (Option α))
    (u : Finset α) (hu : u = a.toFinset ∪ b.toFinset)
    (noreads : ∀ i ∈ u, hits (some i) t = 0 ∧ ¬ outUses (some i) t) :
    ∃ post : Bool → Finset α → Prop, ∀ x : Finset α,
      (.gate a b t : Net α).eval (fun i => decide (i ∈ x)) = true ↔
      post (decide (a.toFinset ⊆ x ∩ u ∨ b.toFinset ⊆ x ∩ u)) (x \ u) := by
  classical
  refine ⟨fun h rest => t.eval (fun z => z.elim h (fun i => decide (i ∈ rest))) = true, ?_⟩
  intro x
  apply Iff.of_eq
  congr 1
  rw [Net.eval]
  apply eval_congr_used
  intro z used
  cases z with
  | none =>
    simp only [Option.elim_none]
    apply Bool.eq_iff_iff.mpr
    simp only [Bool.or_eq_true, List.all_eq_true, decide_eq_true_eq,Finset.subset_inter_iff]
    have ha : a.toFinset ⊆ u := hu ▸ Finset.subset_union_left
    have hb : b.toFinset ⊆ u := hu ▸ Finset.subset_union_right
    simp [ha,hb,Finset.subset_iff]
  | some i =>
    simp only [Option.elim_some]
    by_cases hi : i ∈ u
    · obtain ⟨hz,ho⟩ := noreads i hi
      rcases used with h|h
      · omega
      · exact (ho h).elim
    · simp [hi]

end FreeAndNet

namespace FreeAndNet
open ThresholdFactors

theorem gate_repeat {α : Type} [Fintype α] [DecidableEq α] (n : 3 ≤ Fintype.card α)
    (a b : List α) (t : Net (Option α)) (h : Computes (.gate a b t))
    (hu : 2 ≤ (a.toFinset ∪ b.toFinset).card) :
    ∃ i, 2 ≤ hits i (.gate a b t) := by
  classical
  by_contra! hh
  let u := a.toFinset ∪ b.toFinset
  have nh (i) (hi : i ∈ u) : hits (some i) t = 0 ∧ ¬ outUses (some i) t := by
    have hm : i ∈ a ∨ i ∈ b := by simpa [u] using hi
    have hh' := hh i
    simp [hits,hm] at hh'
    exact ⟨by omega, noOutputRaw n h i⟩
  obtain ⟨post,hpost⟩ := gate_cut a b t u rfl nh
  obtain ⟨i, hi, j, hj, hij⟩ := Finset.one_lt_card.mp (show 1 < u.card from hu)
  by_cases whole : u = Finset.univ
  · have hn : 0 < (Finset.univ \ {i,j} : Finset α).card := by
      rw [Finset.card_sdiff_of_subset (Finset.subset_univ _)]
      simp [hij]; omega
    obtain ⟨k,hk⟩ := Finset.card_pos.mp hn
    simp at hk
    apply twoTermsCut i j k hij (Ne.symm hk.1) (Ne.symm hk.2) a.toFinset b.toFinset
        (fun z => post z ∅)
    intro x
    have empty : x \ (Finset.univ : Finset α) = ∅ := Finset.sdiff_eq_empty_iff_subset.mpr (Finset.subset_univ _)
    simpa [whole,empty] using (h x).symm.trans (hpost x)
  · obtain ⟨k, hk⟩ : ∃ k, k ∉ u := by
      by_contra! hc
      exact whole (Finset.eq_univ_of_forall hc)
    apply oneBitCut u i j k hij hi hj hk
      (fun y => decide (a.toFinset ⊆ y ∨ b.toFinset ⊆ y)) post
    intro x
    exact (h x).symm.trans (hpost x)
end FreeAndNet

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

private def Identifies {α} [DecidableEq α] (t : Net α) : Prop :=
  ∀ x : Finset α, t.eval (fun i => decide (i ∈ x)) = true ↔ ThresholdFactors.Two x

private theorem no_out {α : Type} [Fintype α] [DecidableEq α] (hn : 3 ≤ Fintype.card α)
    (p : Product α) : ¬Identifies (.out p) := by
  intro h
  have rich (x : Finset α) (sz : 2 ≤ x.card) := (h x).mpr sz
  cases p with
  | none =>
    have z := rich Finset.univ (by simpa using (show 2 ≤ Fintype.card α by omega))
    contradiction
  | some l =>
    cases l with
    | nil =>
      have z := (h ∅).mp (by rfl)
      simp [ThresholdFactors.Two] at z
    | cons i is =>
      have z := rich (Finset.univ.erase i) (by
        rw [Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ]
        omega)
      simp [Net.eval,pval] at z

private theorem delete_computes {α} [Fintype α] [DecidableEq α] (i : α)
    (t : Net α) (h : Identifies t) :
    let s := fun j : α => if h : j ≠ i then some [(⟨j,h⟩ : {j // j ≠ i})] else none
    Identifies (specialize s t) := by
  dsimp only
  intro x
  let emb : {j // j ≠ i} ↪ α := Function.Embedding.subtype _
  have orig := h (x.map emb)
  rw [eval_specialize]
  have eq : (fun j : α => pval (fun z => decide (z ∈ x))
      (if h : j ≠ i then some [(⟨j,h⟩ : {j // j ≠ i})] else none)) =
      (fun j => decide (j ∈ x.map emb)) := by
    funext j
    by_cases hj : j ≠ i
    · simp [hj,pval,emb,Finset.mem_map]
    · have e := Classical.not_not.mp hj
      subst j
      simp [emb,pval,Finset.mem_map]
  rw [eq]
  simpa only [ThresholdFactors.Two,Finset.card_map] using orig

/-- Induction on OR cost handles both deletion of a degenerate gate and
deletion of a variable eliminating two ORs. -/
theorem lower_of_repeat
    (degenerate : ∀ {α : Type} [DecidableEq α], ∀ (a b : List α) (t : Net (Option α)),
      (a.toFinset ∪ b.toFinset).card ≤ 1 → ∃ u : Net α,
      (∀ v, u.eval v = (Net.gate a b t).eval v) ∧ u.cost < (Net.gate a b t).cost)
    (repeatStep : ∀ {α : Type} [Fintype α] [DecidableEq α],
      3 ≤ Fintype.card α → ∀ (a b : List α) (t : Net (Option α)),
      (∀ x : Finset α, (Net.gate a b t).eval (fun i => decide (i ∈ x)) = true ↔ ThresholdFactors.Two x) →
      2 ≤ (a.toFinset ∪ b.toFinset).card → ∃ i, 2 ≤ hits i (.gate a b t))
    {α : Type} [Fintype α] [DecidableEq α] (t : Net α)
    (h : ∀ x : Finset α, t.eval (fun i => decide (i ∈ x)) = true ↔ ThresholdFactors.Two x) :
    2 * Fintype.card α - 4 ≤ t.cost := by
  generalize hk : t.cost = k
  induction k using Nat.strong_induction_on generalizing α with
  | ind k ih =>
    by_cases hn : 3 ≤ Fintype.card α
    · cases t with
      | out p => exact False.elim (no_out hn p h)
      | gate a b t =>
        by_cases hu : 2 ≤ (a.toFinset ∪ b.toFinset).card
        · obtain ⟨i,hi⟩ := repeatStep hn a b t h hu
          let s := fun j : α => if h : j ≠ i then some [(⟨j,h⟩ : {j // j ≠ i})] else none
          let t' := specialize s (.gate a b t)
          have sav := specialize_saves i s (by simp [s]) (.gate a b t)
          change t'.cost + _ ≤ _ at sav
          have h' : Identifies t' := delete_computes i _ h
          have lower := ih t'.cost (by omega) t' h' rfl
          have card := Fintype.card_subtype_compl (p := fun j : α => j = i)
          change Fintype.card {j // j ≠ i} = Fintype.card α - Fintype.card {j // j = i} at card
          rw [Fintype.card_subtype_eq] at card
          omega
        · obtain ⟨u,he,lt⟩ := degenerate a b t (by omega)
          have h' : Identifies u := fun x => (he _).symm ▸ h x
          exact (ih u.cost (by omega) u h' rfl).trans (by omega)
    · omega
end FreeAndNet

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

namespace FreeAndNet

theorem threshold_two_or_lower {α : Type} [Fintype α] [DecidableEq α]
    (t : Net α) (h : Computes t) : 2 * Fintype.card α - 4 ≤ t.cost :=
  lower_of_repeat (fun a b t hu => delete_degenerate_first a b t (Or.inr (Or.inr hu)))
    (fun hn a b t h hu => gate_repeat hn a b t h hu) t h

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

/-- A monotone binary circuit computing threshold two on n inputs requires
at least 2n−4 physical OR gates. -/
theorem threshold_two_circuit_or_lower (n : ℕ) (C : Circuit) (hm : Monotone2 C)
    (h : ∀ x : Finset (Fin n),
      C.eval (List.ofFn (fun i => decide (i ∈ x))) = true ↔ 2 ≤ x.card) :
    2*n - 4 ≤ (C.gates.filter CircuitCompiler.orFlag).length := by
  have lower := threshold_two_or_lower (CircuitCompiler.compile n C) (fun x => by
    rw [CircuitCompiler.compile_eval n C hm]; exact h x)
  simpa using lower.trans (CircuitCompiler.compile_cost n C)
end FreeAndNet
