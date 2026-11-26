import ThresholdFirstMarkCut
namespace ThresholdOverrideCut
open ResidualSurplus PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdLeakPins
open ThresholdOccurrenceEval ThresholdFirstMarkCut
variable {C : Circuit} {n k : Nat} (L : Layout C n)

/-- none reads the original operand, with all original raw inputs fixed at zero.
An override can replace an internal operand as well as an original raw operand. -/
abbrev Override (C : Circuit) (k : Nat) := Pin C → Option (Bool ⊕ Fin k)

noncomputable def read (O : Override C k) (s : Finset (Fin k)) (p : Pin C)
    (lower : ∀ j : Id C, source L p=n+j.val → Bool) : Bool :=
  by
    classical
    exact match O p with
    | some a => value a s
    | none => if h : ∃ j : Id C, source L p=n+j.val then lower h.choose h.choose_spec else false

private theorem feed_lt {i j : Id C} {b : Bool} (e : source L (i,b)=n+j.val) : j.val < i.val := by
  have h := earlier L (i,b)
  change source L (i,b)<n+i.val at h
  omega

noncomputable def eval (O : Override C k) (s : Finset (Fin k)) (i : Id C) : Bool :=
  act (L.op i)
    (read L O s (i,false) (fun j edge => eval O s j))
    (read L O s (i,true) (fun j edge => eval O s j))
termination_by i.val
decreasing_by all_goals exact feed_lt L edge

private theorem read_agree (O : Override C k) (s t : Finset (Fin k)) (p : Pin C)
    (raw : ∀ x, O p=some (.inr x) → (x∈s ↔ x∈t))
    (lower : O p=none → ∀ j, source L p=n+j.val → eval L O s j=eval L O t j) :
    read L O s p (fun j _ => eval L O s j)=read L O t p (fun j _ => eval L O t j) := by
  classical
  cases o : O p with
  | none =>
    by_cases h : ∃ j : Id C, source L p=n+j.val
    · simpa only [read,o,dif_pos h] using lower o h.choose h.choose_spec
    · simp only [read,o,dif_neg h]
  | some a =>
    cases a with
    | inl c => simp [read,o,value]
    | inr x => simp [read,o,value,raw x o]

theorem cut (O : Override C k) (P : Partition L) (owner : Fin k → Id C)
    (route : ∀ p x, O p=some (.inr x) → owner x=P.first p.1)
    (u : Id C) (s t : Finset (Fin k)) (raw : ∀ x, owner x≠u → (x∈s ↔ x∈t))
    (same : eval L O s u=eval L O t u) (i : Id C) (inside : region L P u i) :
    eval L O s i=eval L O t i := by
  by_cases eq : i=u
  · simpa only [eq] using same
  have away : P.first i≠u := by
    rcases inside with h|h
    · simpa only [P.onMark i h] using eq
    · exact h
  have agree (b : Bool) := read_agree L O s t (i,b)
    (fun x h => raw x (fun e => away ((route (i,b) x h).symm.trans e)))
    (fun _ j e => cut O P owner route u s t raw same j (incoming_gate L P u i inside eq b j e))
  rw [eval,eval]
  exact congrArg₂ (act (L.op i)) (agree false) (agree true)
termination_by i.val
decreasing_by
  have lt := earlier L (i,b)
  change source L (i,b)<n+i.val at lt
  omega

theorem unary (O : Override C k) (P : Partition L) (owner : Fin k → Id C)
    (route : ∀ p x, O p=some (.inr x) → owner x=P.first p.1)
    (u out : Id C) (marked : P.marked out) (family : Finset (Fin k) → Prop)
    (same : ∀ s, family s → ∀ t, family t → ∀ x, owner x≠u → (x∈s ↔ x∈t)) :
    ∃ d : Bool → Bool, ∀ s, family s → eval L O s out=d (eval L O s u) := by
  classical
  let reach := fun v => ∃ t, family t ∧ eval L O t u=v
  let d := fun v => if h : reach v then eval L O h.choose out else false
  refine ⟨d,?_⟩
  intro s hs
  have h : reach (eval L O s u) := ⟨s,hs,rfl⟩
  simp only [d,dif_pos h]
  exact cut L O P owner route u s h.choose (same _ hs _ h.choose_spec.1)
    h.choose_spec.2.symm out (Or.inl marked)
end ThresholdOverrideCut
