import PEqualNP.Defs
import Graph18272Bridge

namespace PEqualNP.Outside.L_meta_4186_aux.Q0

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm

/-- Expanding a list of selected AND gates backwards keeps one copy of each
live wire. Gate numbers in the list are gate indices, while the frontier uses
wire indices. Unreachable selected gates do not introduce extra clauses. -/
def clauseFrontier (n : ℕ) (C : Circuit) :
    List ℕ → Finset ℕ → Finset ℕ
  | [], S => S
  | j :: js, S =>
      if n + j ∈ S then
        clauseFrontier n C js
          (insert (opnd C j 0) (insert (opnd C j 1) (S.erase (n+j))))
      else clauseFrontier n C js S

theorem clauseFrontier_card (n : ℕ) (C : Circuit) (js : List ℕ) (S : Finset ℕ) :
    (clauseFrontier n C js S).card ≤ S.card + js.length := by
  induction js generalizing S with
  | nil => simp [clauseFrontier]
  | cons j js ih =>
    simp only [clauseFrontier, List.length_cons]
    split
    next h =>
      have h₀ := Finset.card_erase_add_one h
      have h₁ := Finset.card_insert_le (opnd C j 1) (S.erase (n+j))
      have h₂ := Finset.card_insert_le (opnd C j 0)
        (insert (opnd C j 1) (S.erase (n+j)))
      have h₃ := ih (insert (opnd C j 0) (insert (opnd C j 1) (S.erase (n+j))))
      omega
    next => have h := ih S; omega

theorem clauseFrontier_semantics (n : ℕ) (C : Circuit) (js : List ℕ)
    (P : ℕ → Prop)
    (pins : ∀ j ∈ js, P (n+j) ↔ P (opnd C j 0) ∧ P (opnd C j 1))
    (S : Finset ℕ) :
    (∀ w ∈ S, P w) ↔ ∀ w ∈ clauseFrontier n C js S, P w := by
  induction js generalizing S with
  | nil => rfl
  | cons j js ih =>
    have ht : ∀ k ∈ js, P (n+k) ↔ P (opnd C k 0) ∧ P (opnd C k 1) :=
      fun k hk => pins k (List.mem_cons_of_mem _ hk)
    simp only [clauseFrontier]
    split
    next h =>
      rw [← ih ht]
      have hp := pins j (List.mem_cons_self)
      simp only [Finset.forall_mem_insert, Finset.mem_erase]
      constructor
      · intro hs
        exact ⟨(hp.mp (hs _ h)).1, (hp.mp (hs _ h)).2,
          fun w hw => hs w hw.2⟩
      · rintro ⟨h₀,h₁,hr⟩ w hw
        by_cases he : w = n+j
        · subst w; exact hp.mpr ⟨h₀,h₁⟩
        · exact hr w ⟨he,hw⟩
    next => exact ih ht S

/-- The primitive leaves may share a raw clause support. Taking an image can
only decrease their count. The input list consists of H followed by its
distinct dirty AND ancestors in decreasing topological order. -/
theorem rawClauses_of_frontier {n : ℕ} (C : Circuit) (H : ℕ)
    (anc : List ℕ) (support : ℕ → Finset (Fin n))
    (holds : (Fin n → Bool) → ℕ → Prop)
    (pins : ∀ x j, j ∈ H :: anc →
      (holds x (n+j) ↔ holds x (opnd C j 0) ∧ holds x (opnd C j 1)))
    (raw : ∀ x w, w ∈ clauseFrontier n C (H :: anc) {n+H} →
      (holds x w ↔ ∃ i ∈ support w, x i = true)) :
    ∃ clauses : Finset (Finset (Fin n)),
      clauses.card ≤ anc.length + 2 ∧
      ∀ x, holds x (n+H) ↔ ∀ A ∈ clauses, ∃ i ∈ A, x i = true := by
  let S := clauseFrontier n C (H :: anc) {n+H}
  refine ⟨S.image support, ?_, ?_⟩
  · have h₁ := Finset.card_image_le (s := S) (f := support)
    have h₂ := clauseFrontier_card n C (H :: anc) {n+H}
    change S.card ≤ _ at h₂
    simp only [Finset.card_singleton, List.length_cons] at h₂
    omega
  · intro x
    have he := clauseFrontier_semantics n C (H :: anc) (holds x) (pins x) {n+H}
    simp at he
    rw [he]
    constructor
    · intro hf A hA
      obtain ⟨w,hw,rfl⟩ := Finset.mem_image.mp hA
      exact (raw x w hw).mp (hf w hw)
    · intro hf w hw
      exact (raw x w hw).mpr (hf _ (Finset.mem_image_of_mem support hw))


/-- Backward closure of a decreasing scan. Children with earlier gate indices
cannot reintroduce a previously processed gate. -/
theorem clauseFrontier_closed {n : ℕ} {C : Circuit} (raw : ℕ → Prop)
    (js : List ℕ) (desc : js.Pairwise (· > ·))
    (pins : ∀ j ∈ js, ∀ b : Fin 2, raw (opnd C j b) ∨
      ∃ k ∈ js, k < j ∧ opnd C j b = n+k)
    (S : Finset ℕ) (hs : ∀ w ∈ S, raw w ∨ ∃ j ∈ js, w = n+j) :
    ∀ w ∈ clauseFrontier n C js S, raw w := by
  induction js generalizing S with
  | nil =>
    intro w hw
    simpa using hs w hw
  | cons j js ih =>
    obtain ⟨before,rest⟩ := List.pairwise_cons.mp desc
    have tailpin : ∀ i ∈ js, ∀ b : Fin 2, raw (opnd C i b) ∨
        ∃ k ∈ js, k < i ∧ opnd C i b = n+k := by
      intro i hi b
      rcases pins i (List.mem_cons_of_mem _ hi) b with h|⟨k,hk,hlt,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨k,(List.mem_cons.mp hk).resolve_left (by have := before i hi; omega),hlt,he⟩
    have old (w) (hw : w ∈ S) (hne : w ≠ n+j) :
        raw w ∨ ∃ k ∈ js, w = n+k := by
      rcases hs w hw with h|⟨k,hk,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨k,(List.mem_cons.mp hk).resolve_left (by omega),he⟩
    have add (b : Fin 2) : raw (opnd C j b) ∨ ∃ k ∈ js, opnd C j b = n+k := by
      rcases pins j List.mem_cons_self b with h|⟨k,hk,hlt,he⟩
      · exact Or.inl h
      · exact Or.inr ⟨k,(List.mem_cons.mp hk).resolve_left (by omega),he⟩
    simp only [clauseFrontier]
    split
    next h =>
      apply ih rest tailpin
      intro w hw
      simp only [Finset.mem_insert, Finset.mem_erase] at hw
      rcases hw with rfl|rfl|⟨hne,hw⟩
      · exact add 0
      · exact add 1
      · exact old _ hw hne
    next h =>
      exact ih rest tailpin S (fun w hw => old w hw (fun he => h (he ▸ hw)))

end PEqualNP.Outside.L_meta_4186_aux.Q0
