import Research.SparseQueryCut
import Research.IncidenceInitial

namespace ScalarLocalGates
open CircuitRewire SparseIncidence SparseQueryCut IncidenceRobust

def row {n : ℕ} (p : Fin n) (T : Finset (Fin n)) : Input n :=
  (single p, fun l => decide (l ∈ T))

def wires {n : ℕ} (X : ℕ → Set (Input n)) (p : Fin n) (j : ℕ) : Set (Finset (Fin n)) :=
  row p ⁻¹' X j

noncomputable def localSlots {n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (s : ℕ) (X : ℕ → Set (Input n)) (p : Fin n) : Finset ℕ :=
  slots (n+n) s (wires X p) (lines I p)

theorem each {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I] (hq : 0<q)
    (hn : n=q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l}=q+1)
    (unique : ∀ p r, p ≠ r → ∃! l, I p l ∧ I r l)
    (s o : ℕ) (X : ℕ → Set (Input n)) (ho : o < n+n+s)
    (inputs : ∀ p : Fin n, X p.val = {z | z.1 p = true} ∧ X (n+p.val) = {z | z.2 p = true})
    (steps : ∀ k < s, ∃ a < n+n+k, ∃ b < n+n+k,
      X (n+n+k) = X a ∪ X b ∨ X (n+n+k) = X a ∨ X (n+n+k) = ∅ ∨ X (n+n+k) = X a ∩ X b)
    (pos : ∀ p l, I p l → (single p,single l) ∈ X o)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l = true} ≤ q → (outside I b,b) ∉ X o)
    (p : Fin n) : q ≤ (localSlots I s X p).card := by
  classical
  let W := wires X p
  have up (j : ℕ) (hj : j < n+n+s) : Upward (X j) := by
    obtain ⟨S,sub,_,sup⟩ := IncidenceBound.support (n+n) s X steps j hj
    intro u v le
    apply sup u v
    intro k hk
    have kb := Finset.mem_range.mp (sub hk)
    by_cases lo : k<n
    · let a : Fin n := ⟨k,lo⟩
      rw [(inputs a).1]; exact le.1 a
    · let b : Fin n := ⟨k-n,by omega⟩
      have e : k=n+b.val := by dsimp [b]; omega
      rw [e,(inputs b).2]; exact le.2 b
  obtain ⟨raw,ord,sem⟩ := select_gates _ _ X steps
  have laws (k : ℕ) (hk : k<s) : W (n+n+k) = (raw k).eval W := by
    change row p ⁻¹' X (n+n+k) = _
    rw [sem k hk,preimage_gate]
    rfl
  have card := lines_card I degree unique hq hn p
  apply per_query (n+n) s o raw W ho ord laws (lines I p) (lines I p) q card
  · intro j hj
    by_cases left : j<n
    · let a : Fin n := ⟨j,left⟩
      have spec (l : Fin n) : l ∈ profile W j ↔ a=p := by
        rw [mem_profile]; change row p {l} ∈ X a.val ↔ _
        rw [(inputs a).1]; change decide (a=p) = true ↔ a=p; simp
      by_cases eq : a=p
      · right
        intro sub
        have covers : Finset.univ ⊆ lines I p := fun l _ => sub ((spec l).mpr eq)
        have h := Finset.card_le_card covers
        simp only [Finset.card_univ,Fintype.card_fin] at h
        have power : 0 < q^2 := Nat.pow_pos hq
        omega
      · left
        have empty : profile W j = ∅ := Finset.eq_empty_iff_forall_notMem.mpr
          (fun l h => eq ((spec l).mp h))
        simp [empty]
    · let b : Fin n := ⟨j-n,by omega⟩
      have e : j=n+b.val := by dsimp [b]; omega
      left
      have sub : profile W j ⊆ {b} := by
        intro l hl
        rw [mem_profile] at hl
        change row p {l} ∈ X j at hl
        rw [e,(inputs b).2] at hl
        have inc : b ∈ ({l} : Finset _) := of_decide_eq_true hl
        simpa [Finset.mem_singleton,eq_comm] using inc
      simpa using Finset.card_le_card sub
  · intro j hj l T inT hl
    apply up j hj _ hl
    constructor
    · intro a h; exact h
    · intro b h
      have eq : b=l := Finset.mem_singleton.mp (of_decide_eq_true h)
      exact decide_eq_true (eq ▸ inT)
  · intro l hl
    have eq : row p {l} = (single p,single l) := by
      apply Prod.ext
      · rfl
      · funext i; simp [row,single]
    change row p {l} ∈ X o
    rw [eq]
    exact pos _ _ (Finset.mem_filter.mp hl).2
  · intro T small dis h
    let y := fun l : Fin n => decide (l∈T)
    have size : Fintype.card {l // y l=true} ≤ q := by simpa [y,Fintype.card_subtype] using small
    apply neg y size
    apply up o ho (u:=row p T) _ h
    constructor
    · intro a ha
      have eq : a=p := of_decide_eq_true ha
      subst a
      apply decide_eq_true
      rintro ⟨l,inc,sel⟩
      exact Finset.disjoint_left.mp dis (of_decide_eq_true sel) (Finset.mem_filter.mpr ⟨by simp,inc⟩)
    · intro l hl; exact hl

theorem total : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → (100 : ℕ) * x11.card < x2 * x1 → x2 * x1 ≤ ∑ p : Fin x2, (localSlots x3 x9 x12 p).card) := by
  intro q n I _ hq hn degree unique s o _ X ho inputs tagged pos neg _
  have pointwise (p : Fin n) : q ≤ (localSlots I s X p).card :=
    each I (by omega) hn degree unique s o X ho inputs (by
      intro k hk
      obtain ⟨a,ha,b,hb,law⟩ := tagged k hk
      exact ⟨a,ha,b,hb,law.imp_right (Or.imp_right (Or.imp_right And.left))⟩) pos neg p
  simpa using (Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n))) (fun p _ => pointwise p))

end ScalarLocalGates
