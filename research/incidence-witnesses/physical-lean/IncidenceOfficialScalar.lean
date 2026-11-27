import Research.CircuitRewire
import Research.SparseIncidence

namespace IncidenceOfficialScalar
open SparseIncidence CircuitRewire

/-- Exactly the official gate condition, including its exceptional AND indices. -/
def PostedSteps {n : ℕ} (s : ℕ) (marked : Finset ℕ) (X : ℕ → Set (Input n)) : Prop :=
  ∀ k < s, ∃ a < n+n+k, ∃ b < n+n+k,
    X (n+n+k) = X a ∪ X b ∨ X (n+n+k) = X a ∨ X (n+n+k) = ∅ ∨
    X (n+n+k) = X a ∩ X b ∧
      (k ∈ marked ∨ ∃ U V : Set (Fin n → Bool), X a = U ×ˢ Set.univ ∧ X b = Set.univ ×ˢ V)

/-- The original output index and every physical gate are retained. -/
theorem translate {n q s o : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (marked : Finset ℕ) (X : ℕ → Set (Input n)) (ho : o < n+n+s)
    (inputs : ∀ i : Fin n, X i.val = {z | z.1 i=true} ∧ X (n+i.val)={z | z.2 i=true})
    (steps : PostedSteps s marked X)
    (pos : ∀ p l, I p l → (single p,single l) ∈ X o)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l=true} ≤ q → (outside I b,b) ∉ X o) :
    ∃ raw : ℕ → Gate,
      (∀ k<s, (raw k).left<n+n+k ∧ (raw k).right<n+n+k) ∧
      (∀ k<s, X (n+n+k) = (raw k).eval X) ∧
      (∀ a b : Fin n → Bool, Fintype.card {l // b l=true} ≤ q →
        ((a,b) ∈ X o ↔ ∃ p l, a p=true ∧ b l=true ∧ I p l)) := by
  have free : ∀ k<s, ∃ a<n+n+k, ∃ b<n+n+k,
      X (n+n+k)=X a ∪ X b ∨ X (n+n+k)=X a ∨ X (n+n+k)=∅ ∨ X (n+n+k)=X a ∩ X b := by
    intro k hk
    obtain ⟨a,ha,b,hb,law⟩ := steps k hk
    refine ⟨a,ha,b,hb,?_⟩
    rcases law with h|h|h|h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h.1))
  obtain ⟨raw,top,sem⟩ := select_gates (n+n) s X free
  exact ⟨raw,top,sem,sparse_slice I (X o) (wire_upward X inputs free o ho) pos neg⟩

theorem tests_three {n q s o : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (marked : Finset ℕ) (X : ℕ → Set (Input n)) (ho : o < n+n+s) (hq : 3≤q)
    (inputs : ∀ i : Fin n, X i.val = {z | z.1 i=true} ∧ X (n+i.val)={z | z.2 i=true})
    (steps : PostedSteps s marked X)
    (pos : ∀ p l, I p l → (single p,single l) ∈ X o)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l=true} ≤ q → (outside I b,b) ∉ X o)
    (a b : Fin n → Bool) (hb : Fintype.card {l // b l=true} ≤ 3)
    (indep : ∀ p l, a p=true → b l=true → ¬I p l) : (a,b) ∉ X o := by
  obtain ⟨_,_,_,slices⟩ := translate I marked X ho inputs steps pos neg
  intro hit
  obtain ⟨p,l,hp,hl,flag⟩ := (slices a b (hb.trans hq)).mp hit
  exact indep p l hp hl flag

theorem price401 (n s : ℕ) (hn : n=401^2+401+1) (hs : 646425≤s) :
    n*401 ≤ 100*s := by
  subst n
  change 64642403 ≤ 100*s
  omega

#print axioms translate
#print axioms tests_three
#print axioms price401
end IncidenceOfficialScalar
