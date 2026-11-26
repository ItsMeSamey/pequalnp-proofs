import Std
namespace GuardRelease

def allowed {G : Type} (guard : G → Bool) (z : Bool) : Prop :=
  z = false ∨ ∃ j, guard j = true

def pivot (p q z : Bool) : Bool := p ^^ (z && q)

theorem release {G : Type} (guard : G → Bool) (p q : Bool) :
    (∃ z, allowed guard z ∧ pivot p q z = true) ↔
    p = true ∨ ∃ j, (guard j && q) = true := by
  cases p <;> cases q <;> simp [allowed, pivot]

theorem release_family {G T : Type} (guard : G → Bool) (p q : T → Bool) :
    (∃ z, allowed guard z ∧ ∃ i, pivot (p i) (q i) z = true) ↔
    (∃ i, p i = true) ∨ (∃ i j, (guard j && q i) = true) := by
  constructor
  · rintro ⟨z, hz, i, hi⟩
    rcases (release guard (p i) (q i)).mp ⟨z,hz,hi⟩ with h | ⟨j,h⟩
    · exact Or.inl ⟨i,h⟩
    · exact Or.inr ⟨i,j,h⟩
  · rintro (⟨i,h⟩ | ⟨i,j,h⟩)
    · exact ⟨false, Or.inl rfl, i, by simpa [pivot] using h⟩
    · obtain ⟨z,hz,hi⟩ := (release guard (p i) (q i)).mpr (Or.inr ⟨j,h⟩)
      exact ⟨z,hz,i,hi⟩

-- An XOR of monomials. Repeated monomials cancel at evaluation.
abbrev Poly (V : Type) := List (List V)
def mono (x : V → Bool) (m : List V) := m.all x
def eval (x : V → Bool) : Poly V → Bool
  | [] => false
  | m :: p => mono x m ^^ eval x p

def Bounded (p : Poly V) (d : Nat) := ∀ m ∈ p, m.length ≤ d

def mul (p q : Poly V) : Poly V := p.flatMap (fun m => q.map (m ++ ·))

theorem mul_bounded (p q : Poly V) {a b : Nat} (hp : Bounded p a) (hq : Bounded q b) :
    Bounded (mul p q) (a+b) := by
  intro m hm
  simp only [mul, List.mem_flatMap, List.mem_map] at hm
  obtain ⟨u,hu,v,hv,rfl⟩ := hm
  simpa using Nat.add_le_add (hp u hu) (hq v hv)

theorem eval_append (x : V → Bool) (p q : Poly V) :
    eval x (p ++ q) = (eval x p ^^ eval x q) := by
  induction p with
  | nil => simp [eval]
  | cons m t ih => simp [eval, ih]

theorem eval_prefix (x : V → Bool) (m : List V) (q : Poly V) :
    eval x (q.map (m ++ ·)) = (mono x m && eval x q) := by
  induction q with
  | nil => simp [eval]
  | cons a t ih =>
    simp only [List.map_cons, eval, ih, mono, List.all_append]
    bv_decide

theorem eval_mul (x : V → Bool) (p q : Poly V) :
    eval x (mul p q) = (eval x p && eval x q) := by
  induction p with
  | nil => simp [mul, eval]
  | cons m t ih =>
    change eval x ((q.map (m ++ ·)) ++ mul t q) = ((mono x m ^^ eval x t) && eval x q)
    rw [eval_append, eval_prefix, ih]
    bv_decide

-- Option.none denotes the pivot variable. Erasing all pivot occurrences
-- implements Boolean idempotence, including for a non-squarefree input.
def split {V : Type} [DecidableEq V] : Poly (Option V) → Poly V × Poly V
  | [] => ([],[])
  | m :: t =>
    let (p,q) := split t
    if none ∈ m then (p,m.reduceOption :: q) else (m.reduceOption :: p,q)

theorem erase_shorter (m : List (Option V)) (hm : none ∈ m) :
    m.reduceOption.length + 1 ≤ m.length := by
  induction m with
  | nil => simp at hm
  | cons a t ih =>
    cases a with
    | none => simpa [List.reduceOption] using Nat.succ_le_succ (List.length_filterMap_le id t)
    | some v =>
      have ht : none ∈ t := by simpa using hm
      simpa [List.reduceOption] using Nat.succ_le_succ (ih ht)

theorem split_bounded [DecidableEq V] (p : Poly (Option V)) (h : Bounded p (d+1)) :
    Bounded (split p).1 (d+1) ∧ Bounded (split p).2 d := by
  induction p with
  | nil => simp [split, Bounded]
  | cons m t ih =>
    obtain ⟨hl,hr⟩ := ih (fun a ha => h a (List.mem_cons_of_mem _ ha))
    have hm := h m List.mem_cons_self
    by_cases hp : none ∈ m
    · simp only [split, ite_eq_left hp]
      refine ⟨hl,?_⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ht
      · have := erase_shorter m hp
        omega
      · exact hr _ ht
    · simp only [split, ite_eq_right hp]
      refine ⟨?_,hr⟩
      intro a ha
      rcases List.mem_cons.mp ha with rfl | ht
      · exact Nat.le_trans (List.length_filterMap_le id _) hm
      · exact hl _ ht

theorem guard_product_bounded [DecidableEq V] (p : Poly (Option V)) (g : Poly V)
    (hp : Bounded p (d+1)) (hg : Bounded g 1) : Bounded (mul g (split p).2) (d+1) := by
  simpa [Nat.add_comm] using mul_bounded g (split p).2 hg (split_bounded p hp).2

def extend (z : Bool) (x : V → Bool) : Option V → Bool
  | none => z
  | some v => x v

theorem mono_split [DecidableEq V] (z : Bool) (x : V → Bool) (m : List (Option V)) :
    mono (extend z x) m = ((if none ∈ m then z else true) && mono x m.reduceOption) := by
  induction m with
  | nil => rfl
  | cons a t ih =>
    cases a with
    | none =>
      simp only [mono, List.all_cons, extend] at ih ⊢
      simp [List.reduceOption, ih]
      bv_decide
    | some v =>
      simp only [mono, List.all_cons, extend] at ih ⊢
      simp [List.reduceOption, ih, Bool.and_left_comm]

theorem eval_split [DecidableEq V] (z : Bool) (x : V → Bool) (p : Poly (Option V)) :
    eval (extend z x) p = pivot (eval x (split p).1) (eval x (split p).2) z := by
  induction p with
  | nil => simp [eval, split, pivot]
  | cons m t ih =>
    by_cases hm : none ∈ m <;>
      simp only [eval, split, hm, ite_true, ite_false, mono_split z x m, ih, pivot, Bool.true_and] <;>
      bv_decide

theorem eliminate [DecidableEq V] {G T : Type} (x : V → Bool)
    (g : G → Poly V) (p : T → Poly (Option V)) :
    (∃ z, allowed (fun j => eval x (g j)) z ∧ ∃ i, eval (extend z x) (p i) = true) ↔
    (∃ i, eval x (split (p i)).1 = true) ∨
      (∃ i j, eval x (mul (g j) (split (p i)).2) = true) := by
  simp only [eval_split, eval_mul]
  apply release_family

end GuardRelease
