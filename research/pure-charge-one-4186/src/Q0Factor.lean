import Q0Pack
import Q0Projection

namespace PEqualNP.Outside.L_meta_4186_aux.Q0.Factor

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

abbrev Signal (n : ℕ) := (Fin n → Bool) → Bool
abbrev Bank (n : ℕ) := Signal n → Prop

def Available {n : ℕ} (p : Pack n) (f : Signal n) : Prop :=
  ∃ w : p.Wire, ∀ x, p.val w x = f x

def join {n : ℕ} (op : Bool) (f h : Signal n) : Signal n :=
  fun x => if op then f x && h x else f x || h x

theorem emit_available {n : ℕ} (p : Pack n) (op : Bool) {f h : Signal n}
    (hf : Available p f) (hh : Available p h) :
    ∃ q : Pack n, q.gates.length = p.gates.length + 1 ∧
      (∀ s, Available p s → Available q s) ∧ Available q (join op f h) := by
  obtain ⟨a, ha⟩ := hf
  obtain ⟨b, hb⟩ := hh
  refine ⟨p.emit op a b, Pack.length_emit .., ?_, p.last op a b, ?_⟩
  · rintro s ⟨w, hw⟩
    exact ⟨p.lift op a b w, fun x => (p.val_lift op a b w x).trans (hw x)⟩
  · intro x
    simpa [join, ha x, hb x] using p.val_last op a b x

/-- Every logical gate has both operands available at its point of emission. -/
inductive Trace (n : ℕ) : Bank n → ℕ → Prop
  | inputs : Trace n (fun s => ∃ i : Fin n, s = fun x => x i) 0
  | emit {B : Bank n} {k : ℕ} (prev : Trace n B k) (op : Bool)
      {a b : Signal n} (ha : B a) (hb : B b) :
      Trace n (fun s => B s ∨ s = join op a b) (k + 1)

theorem Trace.realize {n : ℕ} {B : Bank n} {k : ℕ} (t : Trace n B k) :
    ∃ p : Pack n, p.gates.length = k ∧ ∀ s, B s → Available p s := by
  induction t with
  | inputs =>
    refine ⟨Pack.empty n, rfl, ?_⟩
    rintro s ⟨i,rfl⟩
    exact ⟨(Pack.empty n).input i, Pack.val_input _ i⟩
  | emit prev op ha hb ih =>
    obtain ⟨p, hlen, hbank⟩ := ih
    obtain ⟨q, hcount, keep, added⟩ := emit_available p op (hbank _ ha) (hbank _ hb)
    refine ⟨q, by omega, ?_⟩
    rintro s (hs | rfl)
    · exact keep _ (hbank _ hs)
    · exact added

def physically {n : ℕ} (B : Bank n) : Option (Signal n) → Prop
  | none => True
  | some s => B s

def project {n : ℕ} : Option (Signal n) → Option (Signal n) → Option (Signal n)
  | none, b => b
  | some a, none => some a
  | some a, some b => some (join true a b)

def andCost {α : Type*} : Option α → Option α → ℕ
  | some _, some _ => 1
  | _, _ => 0

theorem project_step {n : ℕ} {B : Bank n} {k : ℕ} (t : Trace n B k)
    (a b : Option (Signal n)) (ha : physically B a) (hb : physically B b) :
    ∃ B' : Bank n, Trace n B' (k + andCost a b) ∧
      (∀ s, B s → B' s) ∧ physically B' (project a b) := by
  cases a with
  | none => exact ⟨B, t, fun _ h => h, hb⟩
  | some a =>
    cases b with
    | none => exact ⟨B, t, fun _ h => h, ha⟩
    | some b =>
      exact ⟨_, Trace.emit t true ha hb, fun _ h => Or.inl h, Or.inr rfl⟩

def denotation {n : ℕ} (r : Option (Signal n)) (x : Fin n → Bool) : Bool :=
  r.elim true (fun f => f x)

theorem projected_value {n : ℕ} (a b : Option (Signal n)) (x : Fin n → Bool) :
    denotation (project a b) x = (denotation a x && denotation b x) := by
  cases a <;> cases b <;> simp [project, denotation, join]

theorem direct_cost {α : Type*} {a b : Option α} (h : a = none ∨ b = none) :
    andCost a b = 0 := by
  rcases h with rfl | rfl
  · rfl
  · cases a <;> rfl

theorem orList {n : ℕ} (tail : List (Signal n)) (p : Pack n) (head : Signal n)
    (first : Available p head) (rest : ∀ f ∈ tail, Available p f) :
    ∃ q : Pack n, q.gates.length = p.gates.length + tail.length ∧
      (∀ s, Available p s → Available q s) ∧
      Available q (tail.foldl (join false) head) := by
  induction tail generalizing p head with
  | nil => exact ⟨p, rfl, fun _ h => h, first⟩
  | cons f fs ih =>
    obtain ⟨q, hq, keep, added⟩ := emit_available p false first (rest f (by simp))
    obtain ⟨r, hr, keep', built⟩ := ih q (join false head f) added
      (fun s hs => keep _ (rest s (by simp [hs])))
    exact ⟨r, by simp only [List.length_cons]; omega, fun s h => keep' s (keep s h), built⟩

def combined {n : ℕ} (g first : Signal n) (affected unaffected : List (Signal n)) : Signal n :=
  unaffected.foldl (join false) (join true g (affected.foldl (join false) first))

theorem circuit {n : ℕ} {B : Bank n} {k : ℕ} (t : Trace n B k)
    (g first : Signal n) (affected unaffected : List (Signal n))
    (hg : B g) (hf : B first) (ha : ∀ f ∈ affected, B f) (hu : ∀ f ∈ unaffected, B f) :
    ∃ D : Circuit, IsAO2 n D ∧
      circuitFun n D = combined g first affected unaffected ∧
      D.size = k + affected.length + 1 + unaffected.length := by
  obtain ⟨p, hp, old⟩ := t.realize
  obtain ⟨q, hq, keep, af⟩ := orList affected p first (old _ hf) (fun f h => old _ (ha f h))
  obtain ⟨r, hr, keep', product⟩ := emit_available q true (keep _ (old _ hg)) af
  obtain ⟨s, hs, _, out⟩ := orList unaffected r _ product
    (fun f h => keep' _ (keep _ (old _ (hu f h))))
  obtain ⟨w, hw⟩ := out
  exact ⟨s.finish w, s.finish_ao2 w, funext fun x => (s.finish_fun w x).trans (hw x),
    by rw [Pack.finish_size]; omega⟩

theorem shorter_of_two_readers {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) {B : Bank n} {k deleted : ℕ} (t : Trace n B k)
    (g first : Signal n) (affected unaffected : List (Signal n))
    (hg : B g) (hf : B first) (ha : ∀ f ∈ affected, B f) (hu : ∀ f ∈ unaffected, B f)
    (sem : combined g first affected unaffected = graphFun G ∅)
    (account : k + deleted + affected.length + unaffected.length ≤ C.size)
    (two : 2 ≤ deleted) : ¬ IsLeastAO G C := by
  intro least
  obtain ⟨D, hD, funD, sizeD⟩ := circuit t g first affected unaffected hg hf ha hu
  have := least.2.2 D hD (funD.trans sem)
  omega


/-- One instruction per original gate. The source's ordinary wire remains separately
addressable after its occurrence in the projection has been replaced by symbolic true. -/
inductive Kind | source | product | disjunction | cleanOr deriving DecidableEq
structure Row where
  kind : Kind
  left : ℕ
  right : ℕ

structure Layout (n : ℕ) where
  slots : List (Option (Signal n))
  sources : List (Option (Signal n))

def seed (n : ℕ) : Layout n :=
  ⟨List.ofFn (fun i : Fin n => some (fun x => x i)), []⟩

def projectedOr {n : ℕ} : Option (Signal n) → Option (Signal n) → Option (Signal n)
  | some a, some b => some (join false a b)
  | _, _ => none

def readPin {n : ℕ} (s : Layout n) (i : ℕ) := s.slots.getD i none

def next {n : ℕ} (s : Layout n) (r : Row) : Layout n :=
  let a := readPin s r.left
  let b := readPin s r.right
  match r.kind with
  | .source => ⟨s.slots ++ [none], project a b :: s.sources⟩
  | .product => ⟨s.slots ++ [project a b], s.sources⟩
  | .disjunction => ⟨s.slots ++ [projectedOr a b], s.sources⟩
  | .cleanOr => ⟨s.slots ++ [none], s.sources⟩

def price {n : ℕ} (s : Layout n) (r : Row) :=
  if r.kind = .cleanOr then 0 else andCost (readPin s r.left) (readPin s r.right)

def Good {n : ℕ} (B : Bank n) (s : Layout n) :=
  (∀ v ∈ s.slots, physically B v) ∧ (∀ v ∈ s.sources, physically B v)

private theorem phys_mono {n : ℕ} {B D : Bank n} (h : ∀ f, B f → D f)
    (v : Option (Signal n)) (hv : physically B v) : physically D v := by
  cases v with
  | none => trivial
  | some f => exact h f hv

theorem read_good {n : ℕ} {B : Bank n} {s : Layout n} (h : Good B s) (i : ℕ) :
    physically B (readPin s i) := by
  by_cases hi : i < s.slots.length
  · simpa [readPin, List.getD_eq_getElem?_getD, hi] using h.1 s.slots[i] (List.getElem_mem hi)
  · simp [readPin, List.getD_eq_getElem?_getD, List.getElem?_eq_none (Nat.le_of_not_gt hi), physically]

private theorem or_step {n : ℕ} {B : Bank n} {k : ℕ} (t : Trace n B k)
    (a b : Option (Signal n)) (ha : physically B a) (hb : physically B b) :
    ∃ D : Bank n, Trace n D (k + andCost a b) ∧
      (∀ f, B f → D f) ∧ physically D (projectedOr a b) := by
  cases a <;> cases b
  · exact ⟨B,t,fun _ h => h,True.intro⟩
  · exact ⟨B,t,fun _ h => h,True.intro⟩
  · exact ⟨B,t,fun _ h => h,True.intro⟩
  · exact ⟨_,Trace.emit t false ha hb,fun _ h => Or.inl h,Or.inr rfl⟩

private theorem row_step {n : ℕ} {B : Bank n} {k : ℕ} {s : Layout n}
    (t : Trace n B k) (good : Good B s) (r : Row) :
    ∃ D : Bank n, Trace n D (k + price s r) ∧ Good D (next s r) := by
  obtain ⟨kind,l,r⟩ := r
  have hp := project_step t (readPin s l) (readPin s r) (read_good good l) (read_good good r)
  have ho := or_step t (readPin s l) (readPin s r) (read_good good l) (read_good good r)
  cases kind with
  | source =>
    obtain ⟨D, step, keep, new⟩ := hp
    refine ⟨D, by simpa [price] using step, ?_⟩
    constructor
    · intro v hv
      change v ∈ s.slots ++ [none] at hv
      rcases List.mem_append.mp hv with old | last
      · exact phys_mono keep _ (good.1 _ old)
      · obtain rfl := List.mem_singleton.mp last
        trivial
    · intro v hv
      change v ∈ project (readPin s l) (readPin s r) :: s.sources at hv
      rcases List.mem_cons.mp hv with rfl | old
      · exact new
      · exact phys_mono keep _ (good.2 _ old)
  | product =>
    obtain ⟨D, step, keep, new⟩ := hp
    refine ⟨D, by simpa [price] using step, ?_⟩
    constructor
    · intro v hv
      change v ∈ s.slots ++ [_] at hv
      rcases List.mem_append.mp hv with old | last
      · exact phys_mono keep _ (good.1 _ old)
      · obtain rfl := List.mem_singleton.mp last
        exact new
    · exact fun _ hv => phys_mono keep _ (good.2 _ hv)
  | disjunction =>
    obtain ⟨D, step, keep, new⟩ := ho
    refine ⟨D, by simpa [price] using step, ?_⟩
    constructor
    · intro v hv
      change v ∈ s.slots ++ [_] at hv
      rcases List.mem_append.mp hv with old | last
      · exact phys_mono keep _ (good.1 _ old)
      · obtain rfl := List.mem_singleton.mp last
        exact new
    · exact fun _ hv => phys_mono keep _ (good.2 _ hv)
  | cleanOr =>
    refine ⟨B, by simpa [price] using t, ?_⟩
    constructor
    · intro v hv
      change v ∈ s.slots ++ [none] at hv
      rcases List.mem_append.mp hv with old | last
      · exact good.1 _ old
      · obtain rfl := List.mem_singleton.mp last
        trivial
    · exact good.2

def expense {n : ℕ} (s : Layout n) : List Row → ℕ
  | [] => 0
  | r :: rs => price s r + expense (next s r) rs

theorem compileRows {n : ℕ} (rs : List Row) {B : Bank n} {k : ℕ} {s : Layout n}
    (t : Trace n B k) (good : Good B s) : ∃ D : Bank n,
    Trace n D (k + expense s rs) ∧ Good D (rs.foldl next s) := by
  induction rs generalizing B k s with
  | nil => exact ⟨B,t,good⟩
  | cons r rs ih =>
    obtain ⟨D, step, good'⟩ := row_step t good r
    obtain ⟨E, allSteps, final⟩ := ih step good'
    exact ⟨E, by simpa only [expense, Nat.add_assoc] using allSteps, final⟩

theorem compile {n : ℕ} (rs : List Row) : ∃ D : Bank n,
    Trace n D (expense (seed n) rs) ∧ Good D (rs.foldl next (seed n)) := by
  have good : Good (fun s : Signal n => ∃ i : Fin n, s = fun x => x i) (seed n) := by
    constructor
    · intro v hv
      change v ∈ List.ofFn (fun i : Fin n => some (fun x : Fin n → Bool => x i)) at hv
      obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hv
      exact ⟨i,rfl⟩
    · simp [seed]
  simpa using compileRows rs (Trace.inputs (n := n)) good

end PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
