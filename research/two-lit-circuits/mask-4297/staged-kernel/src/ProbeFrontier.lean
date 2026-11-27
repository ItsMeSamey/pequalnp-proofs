import Research.MissingCellRigidity
namespace ProbeFrontier
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Research.MissingCell
abbrev Mask (α : Type) := α → Bool
variable {α : Type} [Fintype α] [DecidableEq α]
def zero : Mask α := fun _ => false
def one : Mask α := fun _ => true
def value (w : α → List Bool) (i : ℕ) : Mask α := fun p => (w p).getD i false
def bank (w : α → List Bool) (I : Finset ℕ) : Finset (Mask α) := I.image (value w)
def available (S : Finset (Mask α)) (a : Mask α) : Prop := a ∈ S ∨ a = zero ∨ a = one
inductive Operation (S : Finset (Mask α)) : Bool → Mask α → Prop where
  | neg (a : Mask α) (ha : available S a) : Operation S true (fun p => !(a p))
  | conj (a b : Mask α) (ha : available S a) (hb : available S b) :
      Operation S false (fun p => a p && b p)
  | disj (a b : Mask α) (ha : available S a) (hb : available S b) :
      Operation S false (fun p => a p || b p)
inductive Run (target : Mask α) : ℕ → ℕ → Finset (Mask α) → Prop where
  | finish (S) (h : available S target) : Run target 0 0 S
  | step {b t : ℕ} {S T : Finset (Mask α)} {neg : Bool} {y : Mask α}
      (op : Operation S neg y) (next : T ⊆ insert y S) (rest : Run target b t T) :
      Run target (b + if neg then 0 else 1) (t + if neg then 1 else 0) S

private theorem operation_of_gate {g : Gate} {w : α → List Bool} {S : Finset (Mask α)}
    (ok : g.op = .and ∨ g.op = .or ∨ g.op = .not) (len : g.inputs.length ≤ 2)
    (readable : ∀ i ∈ g.inputs, available S (value w i)) :
    ∃ neg, Operation S neg (fun p => g.op.eval (g.inputs.map fun i => (w p).getD i false)) := by
  obtain ⟨op,ins⟩ := g
  change op = _ ∨ op = _ ∨ op = _ at ok
  change ins.length ≤ 2 at len
  change ∀ i ∈ ins, available S (value w i) at readable
  change ∃ neg, Operation S neg (fun p => op.eval (ins.map fun i => (w p).getD i false))
  have hz : available S zero := Or.inr (Or.inl rfl)
  have ht : available S one := Or.inr (Or.inr rfl)
  cases ins with
  | nil =>
    rcases ok with rfl|rfl|rfl
    · exact ⟨false,Operation.conj one one ht ht⟩
    · exact ⟨false,Operation.disj zero zero hz hz⟩
    · exact ⟨true,Operation.neg zero hz⟩
  | cons a tl =>
    have ha := readable a (by simp)
    cases tl with
    | nil =>
      rcases ok with rfl|rfl|rfl
      · exact ⟨false,Operation.conj (value w a) one ha ht⟩
      · exact ⟨false,Operation.disj (value w a) zero ha hz⟩
      · exact ⟨true,Operation.neg (value w a) ha⟩
    | cons b tl =>
      have hb := readable b (by simp)
      cases tl with
      | nil =>
        rcases ok with rfl|rfl|rfl
        · exact ⟨false,by simpa [GateOp.eval,value] using Operation.conj (value w a) (value w b) ha hb⟩
        · exact ⟨false,by simpa [GateOp.eval,value] using Operation.disj (value w a) (value w b) ha hb⟩
        · exact ⟨true,Operation.neg (value w a) ha⟩
      | cons d ds => simp at len

theorem simulate (gs : List Gate) (n o : ℕ) (w : α → List Bool)
    (len : ∀ p, (w p).length = n) (legal : FanInTwo ⟨gs,o⟩) :
    ∃ b t, b+t ≤ gs.length ∧ Run (fun p => (Circuit.mk gs o).eval (w p)) b t
      (bank w (live gs n o)) := by
  induction gs generalizing n w with
  | nil =>
    refine ⟨0,0,by simp,Run.finish _ ?_⟩
    change available _ (value w o)
    by_cases h : o<n
    · exact Or.inl (Finset.mem_image.mpr ⟨o,by simp [live,h],rfl⟩)
    · right; left; funext p
      exact getD_missing (by rw [len p]; omega)
  | cons g gs ih =>
    let w' : α → List Bool := fun p => advance g (w p)
    let I := live gs (n+1) o
    let J := live (g::gs) n o
    let y : Mask α := fun p => g.op.eval (g.inputs.map fun i => (w p).getD i false)
    have L : ∀ p, (w' p).length=n+1 := fun p => by simp [w',advance,len p]
    obtain ⟨b,t,sz,run⟩ := ih (n+1) w' L (fun k hk => legal k (List.mem_cons_of_mem _ hk))
    have old (i : ℕ) (hi : i<n) : value w' i = value w i := by
      funext p; exact getD_advance_lt _ _ _ (by rw [len p]; exact hi)
    have newval : value w' n = y := by
      funext p; simpa only [w',y,value,len p] using getD_advance_eq g (w p)
    by_cases used : n ∈ I
    · have ins (i : ℕ) (hi : i ∈ g.inputs) : available (bank w J) (value w i) := by
        by_cases h : i<n
        · left
          apply Finset.mem_image.mpr
          refine ⟨i,?_,rfl⟩
          change i ∈ (if n ∈ I then (I.erase n) ∪ _ else I)
          rw [ite_eq_left used]
          exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨List.mem_toFinset.mpr hi,h⟩)
        · right; left; funext p; exact getD_missing (by rw [len p]; omega)
      have good := legal g (List.mem_cons_self ..)
      have hop : g.op = .and ∨ g.op = .or ∨ g.op = .not := good.1
      obtain ⟨neg,op⟩ := operation_of_gate hop good.2 ins
      have keep : bank w' I ⊆ insert y (bank w J) := by
        intro x hx
        obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hx
        by_cases eq : i=n
        · subst i; simp [newval]
        · have lt := live_lt gs (n+1) o i hi
          rw [old i (by omega)]
          apply Finset.mem_insert_of_mem
          refine Finset.mem_image.mpr ⟨i,?_,rfl⟩
          change i ∈ (if n ∈ I then (I.erase n) ∪ _ else I)
          rw [ite_eq_left used]; exact Finset.mem_union_left _ (Finset.mem_erase.mpr ⟨eq,hi⟩)
      refine ⟨_,_,?_,Run.step op keep run⟩
      cases neg <;> simp_all <;> omega
    · have eq : bank w' I = bank w J := by
        have same : J = I := by change (if n ∈ I then _ else I) = I; simp [used]
        rw [same]
        apply Finset.image_congr
        intro i hi
        have lt := live_lt gs (n+1) o i hi
        have ne : i ≠ n := fun e => used (e ▸ hi)
        exact old i (by omega)
      refine ⟨b,t,by simp; omega,?_⟩
      change Run _ b t (bank w J)
      rw [←eq]; exact run

theorem Run.separates {target : Mask α} {b t : ℕ} {S : Finset (Mask α)}
    (run : Run target b t S) (i j : α) (different : target i ≠ target j) :
    ∃ x ∈ S, x i ≠ x j := by
  by_contra! fail
  apply different
  clear different
  induction run with
  | finish S h =>
    rcases h with h|rfl|rfl
    · exact fail _ h
    · rfl
    · rfl
  | @step b t S T neg y op next rest ih =>
    apply ih
    intro x hx
    have hav (a : Mask α) (ha : available S a) : a i = a j := by
      rcases ha with ha|rfl|rfl
      · exact fail _ ha
      · rfl
      · rfl
    rcases Finset.mem_insert.mp (next hx) with rfl|old
    · cases op with
      | neg a ha => simp [hav a ha]
      | conj a b ha hb => simp [hav a ha,hav b hb]
      | disj a b ha hb => simp [hav a ha,hav b hb]
    · exact fail _ old
end ProbeFrontier
