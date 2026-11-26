import Research.CrownNoDisjointEdges
import Research.CrownFirstTrigger

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

theorem crown_collisions_meet (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (a b c d : Fin C.gates.length) (ab : a ≠ b) (cd : c ≠ d)
    (h₁ : ¬ Disjoint (readAt C.gates 24 a.val) (readAt C.gates 24 b.val))
    (h₂ : ¬ Disjoint (readAt C.gates 24 c.val) (readAt C.gates 24 d.val)) :
    ¬ Disjoint ({a,b} : Finset _) {c,d} := by
  classical
  intro dis
  let S := Finset.univ.filter (fun i : Fin 12 =>
    2 ≤ (trueOrFlags C.gates (oneEach i i)).count true)
  let w (i : S) := oneEach i.val i.val
  let A (i : S) := activeOrIds C.gates (w i)
  let P (g : Fin C.gates.length) := readAt C.gates 24 g.val
  let V (i : S) (x : ℕ) := (C.wires (w i)).getD x false
  have sat (i : S) : (trueOrFlags C.gates (w i)).count true = 2 := by
    have h := (Finset.mem_filter.mp i.property).2
    have ub := crown_trueOrFlags_le i.val C hm rep
    change 2 ≤ (trueOrFlags C.gates (w i)).count true at h
    change (trueOrFlags C.gates (w i)).count true ≤ _ at ub
    omega
  have hit (i : S) (p q : Fin C.gates.length) (pq : p ≠ q) (h : ¬ Disjoint (P p) (P q)) :
      ∃ k ∈ ({p,q} : Finset _), k ∈ A i := by
    by_cases hp : p ∈ A i
    · exact ⟨p,by simp,hp⟩
    by_cases hq : q ∈ A i
    · exact ⟨q,by simp,hq⟩
    exact (h (crown_inactive_pair_disjoint C hm rep ors i.val (sat i) p q pq hp hq)).elim
  have many : 4 ≤ S.card := crown_many_saturated C hm rep size
  have pos (i : Fin 12) (hi : i ∈ S) : 0 < (trueOrFlags C.gates (oneEach i i)).count true :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2) ((Finset.mem_filter.mp hi).2)
  obtain ⟨gate,wire,inj,first⟩ := crown_first_trigger_choice C hm rep size ors S pos
  obtain ⟨u,ua,ub⟩ := Finset.not_disjoint_iff.mp h₁
  obtain ⟨v,vc,vd⟩ := Finset.not_disjoint_iff.mp h₂
  have common (p q : Fin C.gates.length) (x : ℕ) (xp : x ∈ P p) (xq : x ∈ P q) :
      ∀ g ∈ ({p,q} : Finset _), x ∈ P g := by
    intro g hg
    rcases Finset.mem_insert.mp hg with eq | hs
    · exact eq ▸ xp
    · exact (Finset.mem_singleton.mp hs) ▸ xq
  have fires (i : S) (g : Fin C.gates.length) (h : ∃ x ∈ P g, V i x = true) : g ∈ A i := by
    apply (activeOrIds_iff_final_parent C.gates (w i) g).mpr
    have len : (w i).length = 24 := by simp [w,oneEach]
    simpa only [len,P,V,Circuit.wires] using h
  have cap := disjoint_collision_trigger_cap ({a,b} : Finset _) {c,d} dis
    (by simp [ab]) (by simp [cd]) P
    (fun g => readAt_card_le_two _ _ _ (fun g hg => (hm g hg).2))
    A (fun i => (activeOrIds_card ..).trans (sat i))
    (fun i => hit i a b ab h₁) (fun i => hit i c d cd h₂)
    u v (common a b u ua ub) (common c d v vc vd) V fires gate wire inj
    (fun i => (first i).1) (fun i => (first i).2.1) (fun i => (first i).2.2.1)
    (fun i => (first i).2.2.2)
  have su : S.card ≤ 3 := by simpa using cap
  omega

end PEqualNP.Research.MissingCell
