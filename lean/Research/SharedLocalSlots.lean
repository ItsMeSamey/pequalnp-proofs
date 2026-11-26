import Mathlib.Data.Finset.Card
namespace SharedLocalSlots
inductive Expr
  | zero | point (p : ℕ) | line (l : ℕ)
  | join (a b : Expr) | meet (a b : Expr)
  deriving DecidableEq

def eval (x y : ℕ → Prop) : Expr → Prop
  | .zero => False
  | .point p => x p
  | .line l => y l
  | .join a b => eval x y a ∨ eval x y b
  | .meet a b => eval x y a ∧ eval x y b

def gates : Expr → List Expr
  | .point _ | .line _ => []
  | .zero => [.zero]
  | .join a b => gates a ++ gates b ++ [.join a b]
  | .meet a b => gates a ++ gates b ++ [.meet a b]

def col (f : ℕ → ℕ → ℕ) (j : ℕ) : ℕ → Expr
  | 0 => .zero
  | n+1 => .join (col f j n) (.meet (.point n) (.line (f n j)))

def top (f : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → Expr
  | 0 => col f 0 n
  | k+1 => .join (top f n k) (col f (k+1) n)

theorem col_eval (f : ℕ → ℕ → ℕ) (n j : ℕ) (x y : ℕ → Prop) :
    eval x y (col f j n) ↔ ∃ p < n, x p ∧ y (f p j) := by
  induction n with
  | zero => simp [col,eval]
  | succ n ih =>
    change (_ ∨ x n ∧ y (f n j)) ↔ _
    rw [ih]
    constructor
    · rintro (⟨p,hp,h⟩|h)
      · exact ⟨p,by omega,h⟩
      · exact ⟨n,by omega,h⟩
    · rintro ⟨p,hp,h⟩
      by_cases eq : p=n
      · subst p; exact Or.inr h
      · exact Or.inl ⟨p,by omega,h⟩

theorem top_eval (f : ℕ → ℕ → ℕ) (n k : ℕ) (x y : ℕ → Prop) :
    eval x y (top f n k) ↔ ∃ j ≤ k, ∃ p < n, x p ∧ y (f p j) := by
  induction k with
  | zero => simp [top,col_eval]
  | succ k ih =>
    change (_ ∨ _) ↔ _
    rw [ih,col_eval]
    constructor
    · rintro (⟨j,hj,h⟩|h)
      · exact ⟨j,by omega,h⟩
      · exact ⟨k+1,by omega,h⟩
    · rintro ⟨j,hj,h⟩
      by_cases eq : j=k+1
      · subst j; exact Or.inr h
      · exact Or.inl ⟨j,by omega,h⟩

def hit (p l : ℕ) (e : Expr) := eval (· = p) (· = l) e

def Local (f : ℕ → ℕ → ℕ) (q p : ℕ) (e : Expr) : Prop :=
  (∃ a b : ℕ, a ≠ b ∧ hit p a e ∧ hit p b e) ∧
  ∀ l, hit p l e → ∃ j ≤ q, f p j = l

private theorem col_gate_hit (f : ℕ → ℕ → ℕ) (n j p l : ℕ) (e : Expr) (hg : e ∈ gates (col f j n))
    (h : hit p l e) : f p j = l := by
  induction n with
  | zero =>
    have : e = .zero := by simpa [col,gates] using hg
    subst e; exact False.elim h
  | succ n ih =>
    change e ∈ gates (.join _ _) at hg
    simp only [gates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hg
    rcases hg with (old|rfl)|rfl
    · exact ih old
    · change n=p ∧ f n j=l at h
      exact h.1 ▸ h.2
    · have ⟨a,_,eq,yes⟩ := (col_eval f (n+1) j (· = p) (· = l)).mp h
      exact eq ▸ yes

private theorem col_not_local (f : ℕ → ℕ → ℕ) (n j q p : ℕ) (e : Expr)
    (hg : e ∈ gates (col f j n)) : ¬ Local f q p e := by
  rintro ⟨⟨a,b,ne,ha,hb⟩,_⟩
  exact ne ((col_gate_hit f n j p a e hg ha).symm.trans (col_gate_hit f n j p b e hg hb))

private theorem merged_local (f : ℕ → ℕ → ℕ) (n k q p : ℕ) (hp : p<n) (hk : k+1 ≤ q)
    (diff : f p 0 ≠ f p 1) : Local f q p (top f n (k+1)) := by
  constructor
  · refine ⟨f p 0,f p 1,diff,?_,?_⟩
    · exact (top_eval _ _ _ _ _).mpr ⟨0,by omega,p,hp,rfl,rfl⟩
    · exact (top_eval _ _ _ _ _).mpr ⟨1,by omega,p,hp,rfl,rfl⟩
  · intro l h
    obtain ⟨j,hj,a,_,e,h'⟩ := (top_eval _ _ _ _ _).mp h
    exact ⟨j,by omega,e ▸ h'⟩

def merges (f : ℕ → ℕ → ℕ) (n : ℕ) : ℕ → List Expr
  | 0 => []
  | k+1 => merges f n k ++ [top f n (k+1)]

noncomputable def row_local_list (f : ℕ → ℕ → ℕ) (q p : ℕ) (e : Expr) : List Expr := by
  classical
  exact (gates e).filter (fun g => decide (Local f q p g))

theorem all_local_coincide (f : ℕ → ℕ → ℕ) (n k q p : ℕ) (hp : p<n) (hk : k≤q)
    (diff : f p 0 ≠ f p 1) : row_local_list f q p (top f n k) = merges f n k := by
  classical
  have col_empty (j : ℕ) : (gates (col f j n)).filter (fun e => decide (Local f q p e)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro e he
    simp [col_not_local f n j q p e he]
  induction k with
  | zero => exact col_empty 0
  | succ k ih =>
    have good := merged_local f n k q p hp hk diff
    unfold row_local_list at ih ⊢
    change (gates (top f n k) ++ gates (col f (k+1) n) ++ [top f n (k+1)]).filter _ = _
    simp [List.filter_append,ih (by omega),col_empty,good,merges]

theorem merge_count (f : ℕ → ℕ → ℕ) (n k : ℕ) : (merges f n k).length = k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [merges,ih]

end SharedLocalSlots
