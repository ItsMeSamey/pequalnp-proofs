import IncidenceOfficialScalar

namespace IncidenceOfficialScalar
open SparseIncidence CircuitRewire

/-- Physical bridge still required of the order-401 circuit lower bound. -/
def ScalarLower401 : Prop :=
  ∀ (n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I], n=401^2+401+1 →
    (∀ l : Fin n, Fintype.card {p // I p l}=401+1) →
    (∀ p p' : Fin n, p≠p' → ∃! l, I p l ∧ I p' l) →
    ∀ (s o : ℕ) (raw : ℕ → Gate) (X : ℕ → Set (Input n)), o<n+n+s →
    (∀ i : Fin n, X i.val={z | z.1 i=true} ∧ X (n+i.val)={z | z.2 i=true}) →
    (∀ k<s, (raw k).left<n+n+k ∧ (raw k).right<n+n+k) →
    (∀ k<s, X (n+n+k)=(raw k).eval X) →
    (∀ p l, I p l → (single p,single l) ∈ X o) →
    (∀ a b : Fin n → Bool, Fintype.card {l // b l=true}≤401 → (∀ p l, a p=true → b l=true → ¬I p l) →
        (a,b) ∉ X o) → 646425≤s

/-- The exact posted binder order at the specific order 401. -/
theorem posted_401 (lower : ScalarLower401) :
    ∀ (n : ℕ) (I : Fin n → Fin n → Prop) [DecidableRel I], 100< (401:ℕ) →
      n=401^2+401+1 → (∀ l : Fin n, Fintype.card {p // I p l}=401+1) →
      (∀ p p' : Fin n, p≠p' → ∃! l, I p l ∧ I p' l) →
      ∀ (s o : ℕ) (marked : Finset ℕ) (X : ℕ→Set (Input n)), o<n+n+s →
        (∀ i : Fin n, X i.val={z | z.1 i=true} ∧ X (n+i.val)={z | z.2 i=true}) →
        PostedSteps s marked X →
        (∀ p l, I p l → (single p,single l) ∈ X o) →
        (∀ b : Fin n → Bool, Fintype.card {l // b l=true}≤401 → (outside I b,b) ∉ X o) →
        100*marked.card<n*401 → n*401≤100*s := by
  intro n I inst _ hn deg uniq s o marked X ho inputs steps pos neg _
  obtain ⟨raw,ord,sem,slices⟩ := translate I marked X ho inputs steps pos neg
  apply price401 n s hn
  apply lower n I hn deg uniq s o raw X ho inputs ord sem pos
  intro a b hb hi hit
  obtain ⟨p,l,hp,hl,flag⟩ := (slices a b hb).mp hit
  exact hi p l hp hl flag

#print axioms posted_401
end IncidenceOfficialScalar
