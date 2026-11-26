import Mathlib.Data.Fintype.Card
import Mathlib.Data.Set.Prod
import Mathlib.Data.Fintype.Powerset

namespace IncidenceBound

theorem support {Z : Type*} (m s : ℕ) (X : ℕ → Set Z)
    (steps : ∀ g < s, ∃ a < m+g, ∃ b < m+g,
      X (m+g) = X a ∪ X b ∨ X (m+g) = X a ∨ X (m+g) = ∅ ∨ X (m+g) = X a ∩ X b)
    (o : ℕ) (ho : o < m+s) :
    ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.card ≤ 1+s ∧
      ∀ u v : Z, (∀ i ∈ S, u ∈ X i → v ∈ X i) → u ∈ X o → v ∈ X o := by
  have reach (k : ℕ) (hk : k ≤ s) (W : Finset ℕ) (hw : ∀ w ∈ W, w < m+k) :
      ∃ S : Finset ℕ, S ⊆ Finset.range m ∧ S.card ≤ W.card+k ∧
        ∀ u v : Z, (∀ i ∈ S, u ∈ X i → v ∈ X i) → ∀ w ∈ W, u ∈ X w → v ∈ X w := by
    induction k generalizing W with
    | zero =>
      exact ⟨W,fun w h => Finset.mem_range.mpr (by simpa using hw w h),by omega,fun _ _ h => h⟩
    | succ k ih =>
      let w := m+k
      by_cases use : w ∈ W
      · obtain ⟨a,ha,b,hb,parent⟩ := steps k (by omega)
        let U := insert a (insert b (W.erase w))
        have bounds : ∀ u ∈ U, u < w := by
          intro u hu
          rcases Finset.mem_insert.mp hu with rfl|h
          · exact ha
          rcases Finset.mem_insert.mp h with rfl|h
          · exact hb
          obtain ⟨ne,inc⟩ := Finset.mem_erase.mp h
          have bound := hw u inc
          change u ≠ m+k at ne
          change u < m+k
          omega
        obtain ⟨S,hS,c,dep⟩ := ih (by omega) U bounds
        have uc : U.card ≤ W.card+1 := by
          have c1 := Finset.card_insert_le a (insert b (W.erase w))
          have c2 := Finset.card_insert_le b (W.erase w)
          rw [Finset.card_erase_of_mem use] at c2
          have := Finset.card_pos.mpr ⟨_,use⟩
          dsimp [U]; omega
        refine ⟨S,hS,by omega,?_⟩
        intro x y agree u hu
        by_cases eq : u = w
        · subst u
          have pa := dep x y agree a (by simp [U])
          have pb := dep x y agree b (by simp [U])
          dsimp [w]
          rcases parent with union|copy|empty|inter
          · rw [union]; exact Or.imp pa pb
          · rw [copy]; exact pa
          · rw [empty]; exact id
          · rw [inter]; exact fun h => ⟨pa h.1,pb h.2⟩
        · exact dep x y agree u (by simp [U,eq,hu])
      · have bounds : ∀ u ∈ W, u < w := by
          intro u hu
          have ne : u ≠ w := fun eq => use (eq ▸ hu)
          have bound := hw u hu
          change u ≠ m+k at ne
          change u < m+k
          omega
        obtain ⟨S,hS,c,h⟩ := ih (by omega) W bounds
        exact ⟨S,hS,by omega,h⟩
  obtain ⟨S,hS,c,dep⟩ := reach s le_rfl {o} (by simpa using ho)
  exact ⟨S,hS,by simpa using c,fun u v h => dep u v h o (by simp)⟩

theorem bound : (∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [_x4 : DecidableRel x3],   (100 : ℕ) < x1 →     x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) →       (∀ (x7 : Fin x2), Fintype.card { x8 : Fin x2 // x3 x8 x7 } = x1 + (1 : ℕ)) →         (∀ (x8 x9 : Fin x2), x8 ≠ x9 → ∃! x11 : Fin x2, x3 x8 x11 ∧ x3 x9 x11) →           ∀ (x9 x10 : ℕ) (x11 : Finset ℕ) (x12 : ℕ → Set ((Fin x2 → Bool) × (Fin x2 → Bool))),             x10 < x2 + x2 + x9 →               (∀ (x14 : Fin x2), x12 ↑x14 = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.1 x14 = Bool.true} ∧ x12 (x2 + ↑x14) = {x15 : (Fin x2 → Bool) × (Fin x2 → Bool) | x15.2 x14 = Bool.true}) →                 (∀ x15 < x9,                     ∃ x17 < x2 + x2 + x15,                       ∃ x18 < x2 + x2 + x15,                         have x19 : Set ((Fin x2 → Bool) × (Fin x2 → Bool)) := x12 (x2 + x2 + x15);                         x19 = x12 x17 ∪ x12 x18 ∨ x19 = x12 x17 ∨ x19 = ∅ ∨ x19 = x12 x17 ∩ x12 x18 ∧ (x15 ∈ x11 ∨ ∃ (x20 : Set (Fin x2 → Bool)) (x21 : Set (Fin x2 → Bool)), x12 x17 = x20 ×ˢ Set.univ ∧ x12 x18 = Set.univ ×ˢ x21)) →                   (∀ (x16 x17 : Fin x2), x3 x16 x17 → (fun (x19 : Fin x2) => Decidable.decide (x19 = x16), fun (x19 : Fin x2) => Decidable.decide (x19 = x17)) ∈ x12 x10) → (∀ (x17 : Fin x2 → Bool), Fintype.card { x18 : Fin x2 // x17 x18 = Bool.true } ≤ x1 → (fun (x19 : Fin x2) => Decidable.decide ¬∃ (x20 : Fin x2), x3 x19 x20 ∧ x17 x20 = Bool.true, x17) ∉ x12 x10) → x2 + x2 ≤ x9 + 1) := by
  intro q N I inst hq hN degrees unique s o tags X ho inputs steps pos neg
  obtain ⟨S,hS,card,dep⟩ := support (N+N) s X (by
    intro g hg
    obtain ⟨a,ha,b,hb,law⟩ := steps g hg
    exact ⟨a,ha,b,hb,law.imp_right (Or.imp_right (Or.imp_right And.left))⟩) o ho
  let one := fun (a b : Fin N) => decide (b = a)
  let avoid := fun (y : Fin N → Bool) (p : Fin N) => decide (¬ ∃ l, I p l ∧ y l = true)
  have force (p l : Fin N) (inc : I p l) (y : Fin N → Bool)
      (hy : Fintype.card {k : Fin N // y k = true} ≤ q) :
      ∃ i ∈ S, (one p,one l) ∈ X i ∧ (avoid y,y) ∉ X i := by
    by_contra! h
    apply neg y hy
    exact dep _ _ h (pos p l inc)
  have both (p l : Fin N) (inc : I p l) : p.val ∈ S ∧ N+l.val ∈ S := by
    constructor
    · obtain ⟨i,hi,from',to'⟩ := force p l inc (one l) (by simp [one]; omega)
      by_cases h : i < N
      · let j : Fin N := ⟨i,h⟩
        rw [(inputs j).1] at from'
        have eq : j = p := of_decide_eq_true from'
        exact eq ▸ (show j.val ∈ S from hi)
      · have lim := Finset.mem_range.mp (hS hi)
        let j : Fin N := ⟨i-N,by omega⟩
        have e : i = N+j.val := by dsimp [j]; omega
        rw [e,(inputs j).2] at from' to'
        exact False.elim (to' from')
    · obtain ⟨i,hi,from',to'⟩ := force p l inc (fun _ => false) (by simp)
      by_cases h : i < N
      · let j : Fin N := ⟨i,h⟩
        rw [(inputs j).1] at to'
        apply False.elim
        apply to'
        change avoid _ j = true
        simp [avoid]
      · have lim := Finset.mem_range.mp (hS hi)
        let j : Fin N := ⟨i-N,by omega⟩
        have e : i = N+j.val := by dsimp [j]; omega
        rw [e,(inputs j).2] at from'
        have eq : j = l := of_decide_eq_true from'
        rw [← eq, ← e]
        exact hi
  have allBits : Finset.range (N+N) ⊆ S := by
    intro v hv
    have bound := Finset.mem_range.mp hv
    by_cases point : v < N
    · let p : Fin N := ⟨v,point⟩
      have big : 2 ≤ N := by omega
      let p' : Fin N := if p.val=0 then ⟨1,by omega⟩ else ⟨0,by omega⟩
      have ne : p ≠ p' := by
        intro e
        have eq := congrArg Fin.val e
        unfold p' at eq
        split at eq
        · change p.val = 1 at eq; omega
        · change p.val = 0 at eq; contradiction
      obtain ⟨l,hl,_⟩ := unique p p' ne
      exact (both p l hl.1).1
    · let l : Fin N := ⟨v-N,by omega⟩
      have nonempty : Nonempty {p : Fin N // I p l} := Fintype.card_pos_iff.mp (by rw [degrees]; omega)
      obtain ⟨⟨p,hp⟩⟩ := nonempty
      have e : N+l.val = v := by dsimp [l]; omega
      exact e ▸ (both p l hp).2
  have count := Finset.card_le_card allBits
  simp only [Finset.card_range] at count
  omega

theorem smallOrder {N q s : ℕ} (hN : N = q^2+q+1) (hq : 100 < q) (upper : q ≤ 199)
    (linear : N+N ≤ s+1) : N*q ≤ 100*s := by
  have := Nat.mul_le_mul_left N upper
  omega

end IncidenceBound
