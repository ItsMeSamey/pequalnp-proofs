import IncidenceStartNormalization
namespace IncidenceHoistFlow
open CircuitRewire IncidenceStartNormalization

def keep (g : Gate) (b : Bool) := if b then g.left else g.right
def other (g : Gate) (b : Bool) := if b then g.right else g.left

/-- Bypassed ORs read their retained predecessor from the rebuilt prefix. -/
def value {Z : Type} (raw : ℕ → Set Z) (code : ℕ → Gate) (choice : ℕ → Option Bool)
    (inputs : ℕ) : ℕ → ℕ → Set Z
  | 0 => raw
  | t+1 =>
    let old := value raw code choice inputs t
    let g := code t
    put old (inputs+t) (match choice t with
      | none => g.eval old
      | some b => old (keep g b))

theorem stable {Z : Type} (X : ℕ → Set Z) (code : ℕ → Gate) (sel : ℕ → Option Bool)
    (m t k : ℕ) (i : ℕ) (hi : i < m+t) :
    value X code sel m (t+k) i = value X code sel m t i := by
  induction k with
  | zero => rfl
  | succ k ih =>
    change put _ (m+(t+k)) _ i = _
    simp only [put,if_neg (show i ≠ m+(t+k) by omega)]
    exact ih

theorem law {Z : Type} (X : ℕ → Set Z) (code : ℕ → Gate) (sel : ℕ → Option Bool)
    (m s j : ℕ) (hj : j < s)
    (ord : (code j).left < m+j ∧ (code j).right < m+j) :
    let Y := value X code sel m s
    Y (m+j) = match sel j with
      | none => (code j).eval Y
      | some b => Y (keep (code j) b) := by
  dsimp only
  have endEq (i : ℕ) (hi : i < m+j+1) :
      value X code sel m s i = value X code sel m (j+1) i := by
    have eq : s=(j+1)+(s-(j+1)) := by omega
    conv_lhs => rw [eq]
    exact stable _ _ _ _ _ _ _ (by omega)
  have prev (i : ℕ) (hi : i < m+j) :
      value X code sel m s i = value X code sel m j i := by
    have eq : s=j+(s-j) := by omega
    conv_lhs => rw [eq]
    exact stable _ _ _ _ _ _ _ hi
  rw [endEq (m+j) (by omega)]
  simp only [value,put,if_pos rfl]
  cases h : sel j with
  | none => simp [Gate.eval,prev _ ord.1,prev _ ord.2]
  | some b =>
    cases b <;> simp [keep,prev _ ord.1,prev _ ord.2]

def lost {Z : Type} (s : ℕ) (code : ℕ → Gate) (sel : ℕ → Option Bool)
    (Y : ℕ → Set Z) : Set Z :=
  { z | ∃ j<s, ∃ b, sel j = some b ∧ z ∈ Y (other (code j) b) }
private theorem eval_sandwich {Z : Type} (g : Gate) {X Y : ℕ → Set Z} {L : Set Z}
    (left : Y g.left ⊆ X g.left ∧ X g.left ⊆ Y g.left ∪ L)
    (right : Y g.right ⊆ X g.right ∧ X g.right ⊆ Y g.right ∪ L) :
    g.eval Y ⊆ g.eval X ∧ g.eval X ⊆ g.eval Y ∪ L := by
  rcases g with ⟨op,l,r⟩
  cases op <;> simp only [Gate.eval,Op.eval] at * <;> grind

/-- Every lost original assignment reaches a rebuilt sibling. -/
theorem sandwich {Z : Type} (m s : ℕ) (X : ℕ → Set Z) (code : ℕ → Gate) (sel : ℕ → Option Bool)
    (order : ∀ j<s, (code j).left<m+j ∧ (code j).right<m+j)
    (original : ∀ j<s, X (m+j)=(code j).eval X)
    (onlyOR : ∀ j<s, ∀ b, sel j=some b → (code j).op=.join) :
    let Y := value X code sel m s
    ∀ i<m+s, Y i ⊆ X i ∧ X i ⊆ Y i ∪ lost s code sel Y := by
  intro Y i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro bound
    by_cases raw : i<m
    · have eq : Y i=X i := by
        simpa only [Nat.zero_add,value] using stable X code sel m 0 s i (by omega)
      rw [eq]
      exact ⟨fun _ h => h,fun _ h => Or.inl h⟩
    · let j := i-m
      have atGate : i=m+j := by dsimp [j]; omega
      have js : j<s := by omega
      have ⟨hl,hr⟩ := order j js
      have pl := ih (code j).left (by omega) (by omega)
      have pr := ih (code j).right (by omega) (by omega)
      rw [atGate, original j js]
      have rebuilt := law X code sel m s j js ⟨hl,hr⟩
      change Y (m+j) = _ at rebuilt
      rw [rebuilt]
      cases chosen : sel j with
      | none => exact eval_sandwich _ pl pr
      | some b =>
        have op := onlyOR j js b chosen
        have spill : Y (other (code j) b) ⊆ lost s code sel Y :=
          fun _ h => ⟨j,js,b,chosen,h⟩
        cases b <;> simp only [keep,other,Gate.eval,op,Op.eval,if_true,
          Bool.false_eq_true,if_false] at * <;> grind

#print axioms law
#print axioms sandwich
end IncidenceHoistFlow
