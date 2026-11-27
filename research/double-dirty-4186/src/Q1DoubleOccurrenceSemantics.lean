import Q1DoubleLedger

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.S4183.S98

/-- In an AND region with a single output every input satisfies the output exactly
when it satisfies all boundary pin occurrences. Duplicate occurrences are retained. -/
theorem occurrence_semantics (n : ℕ) (C : Circuit) (ao : IsAO2 n C)
    (js : Finset ℕ) (root : ℕ) (hr : root ∈ js)
    (ands : ∀ j ∈ js, j < C.gates.length ∧ (gateAt C j).op = GateOp.and)
    (used : ∀ j ∈ js.erase root, ∃ p ∈ pins js, opnd C p.1 p.2 = n+j)
    (x : Fin n → Bool) :
    W n C x (n+root) = true ↔ ∀ p ∈ occurrences n C js, W n C x (opnd C p.1 p.2) = true := by
  classical
  let V := W n C x
  have pinRule (j : ℕ) (hj : j ∈ js) :
      (∀ b, opnd C j b < n+j) ∧
      (V (n+j) = true ↔ ∀ b, V (opnd C j b) = true) := by
    obtain ⟨hlt, hand⟩ := ands j hj
    obtain ⟨_, a, b, ins, ha, hb⟩ := AO_of_IsAO2 n C ao j hlt
    have p0 : opnd C j 0 = a := by simp [opnd, ins]
    have p1 : opnd C j 1 = b := by simp [opnd, ins]
    constructor
    · intro k
      fin_cases k <;> simp_all
    · change W n C x (n+j) = true ↔ _
      rw [W_and n C x j hlt hand a b ins ha hb, Bool.and_eq_true]
      constructor
      · rintro ⟨va,vb⟩ k
        fin_cases k
        · simpa [p0,V] using va
        · simpa [p1,V] using vb
      · intro both
        exact ⟨by simpa [p0,V] using both 0, by simpa [p1,V] using both 1⟩
  constructor
  · intro yes
    have active (d : ℕ) : ∀ j ∈ js, C.gates.length - j = d → V (n+j) = true := by
      induction d using Nat.strong_induction_on with
      | _ d ih =>
        intro j hj hd
        by_cases e : j = root
        · simpa [e,V] using yes
        · obtain ⟨p,hp,peq⟩ := used j (Finset.mem_erase.mpr ⟨e,hj⟩)
          have parent : p.1 ∈ js := (Finset.mem_product.mp hp).1
          have prior := (pinRule p.1 parent).1 p.2
          have lt := (ands p.1 parent).1
          have vp := ih (C.gates.length - p.1) (by omega) p.1 parent rfl
          simpa [peq] using ((pinRule p.1 parent).2.mp vp p.2)
    intro p hp
    have pj : p.1 ∈ js := (Finset.mem_product.mp (Finset.mem_sdiff.mp hp).1).1
    exact (pinRule p.1 pj).2.mp (active _ _ pj rfl) p.2
  · intro boundary
    have active (j : ℕ) : j ∈ js → V (n+j) = true := by
      induction j using Nat.strong_induction_on with
      | _ j ih =>
        intro hj
        apply (pinRule j hj).2.mpr
        intro b
        have pin : (j,b) ∈ pins js := Finset.mem_product.mpr ⟨hj,Finset.mem_univ _⟩
        by_cases int : (j,b) ∈ internal n C js
        · obtain ⟨k,hk,e⟩ := (Finset.mem_filter.mp int).2
          change opnd C j b = n+k at e
          have hlt := (pinRule j hj).1 b
          rw [e]
          exact ih k (by omega) hk
        · exact boundary (j,b) (Finset.mem_sdiff.mpr ⟨pin,int⟩)
    exact active root hr

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
