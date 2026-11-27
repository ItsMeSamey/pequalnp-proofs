import Resolution
namespace Research.Graph9822Resolution

def wireUnion (w v : Wire) : Wire := fun j => w j || v j

theorem resolved_union (g : Gate) (side a b c d : Bool) :
    resolved g side (a || b) (c || d) = (resolved g side a c || resolved g side b d) := by
  cases hg : g.isAnd <;> cases side <;> cases a <;> cases b <;> cases c <;> cases d <;> simp [resolved,hg]

theorem resolve_union (gs : List Gate) (i : Nat) (s w v : Wire) :
    resolve gs i s (wireUnion w v) = wireUnion (resolve gs i s w) (resolve gs i s v) := by
  induction gs generalizing i w v with
  | nil => rfl
  | cons g tail ih =>
    simp only [resolve]
    have hu : Function.update (wireUnion w v) i
        (resolved g (s i) (wireUnion w v g.left) (wireUnion w v g.right)) =
        wireUnion (Function.update w i (resolved g (s i) (w g.left) (w g.right)))
          (Function.update v i (resolved g (s i) (v g.left) (v g.right))) := by
      funext j
      by_cases h : j=i
      · subst j; simp [wireUnion,resolved_union]
      · simp [wireUnion, Function.update_of_ne h]
    rw [hu,ih]

theorem resolve_empty (gs : List Gate) (i : Nat) (s : Wire) :
    resolve gs i s (fun _ => false) = fun _ => false := by
  induction gs generalizing i with
  | nil => rfl
  | cons g tail ih =>
    simp only [resolve]
    have h : Function.update (fun _ : Nat => false) i (resolved g (s i) false false) = fun _ => false := by
      funext j
      by_cases h : j=i
      · subst j; cases hg : g.isAnd <;> cases hs : s i <;> simp [resolved,hg,hs]
      · simp [Function.update_of_ne h]
    rw [h,ih]

def inputSet : List Nat → Wire
  | [] => fun _ => false
  | a :: xs => wireUnion (fun j => decide (j=a)) (inputSet xs)

theorem resolve_inputs (gs : List Gate) (i : Nat) (s : Wire) (xs : List Nat) (out : Nat) :
    resolve gs i s (inputSet xs) out =
      xs.any (fun a => resolve gs i s (fun j => decide (j=a)) out) := by
  induction xs with
  | nil => simp [inputSet,resolve_empty]
  | cons a xs ih => simp [inputSet,resolve_union,wireUnion,ih]

theorem accepts_iff_reaches (gs : List Gate) (i : Nat) (xs : List Nat) (out : Nat) :
    eval gs i (inputSet xs) out = true ↔
      ∀ s, xs.any (fun a => resolve gs i s (fun j => decide (j=a)) out) = true := by
  simp only [eval_iff_all_resolutions, resolve_inputs]

/-- A false input set which becomes true after adding any missing raw forces a
single direction whose reached support is exactly the complementary set on the
selected input alphabet. -/
theorem maximal_witness (gs : List Gate) (i : Nat) (xs : List Nat) (out : Nat)
    (reject : eval gs i (inputSet xs) out = false)
    (maximal : ∀ a, a < i → a ∉ xs → eval gs i (inputSet (a :: xs)) out = true) :
    ∃ s : Wire, ∀ a, a < i →
      (resolve gs i s (fun j => decide (j = a)) out = true ↔ a ∉ xs) := by
  classical
  obtain ⟨s, _, hs⟩ := attains gs i (inputSet xs)
  have empty : xs.any (fun a => resolve gs i s (fun j => decide (j=a)) out) = false := by
    rw [←resolve_inputs,hs,reject]
  refine ⟨s, ?_⟩
  intro a hi
  constructor
  · intro ha hin
    have h : xs.any (fun a => resolve gs i s (fun j => decide (j=a)) out) = true :=
      List.any_eq_true.mpr ⟨a,hin,ha⟩
    simp [empty] at h
  · intro h
    have hit := (accepts_iff_reaches gs i (a::xs) out).mp (maximal a hi h) s
    simpa [empty] using hit

end Research.Graph9822Resolution
#print axioms Research.Graph9822Resolution.resolve_union
#print axioms Research.Graph9822Resolution.resolve_empty
#print axioms Research.Graph9822Resolution.accepts_iff_reaches
#print axioms Research.Graph9822Resolution.maximal_witness
