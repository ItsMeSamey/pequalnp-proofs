import Mathlib.Combinatorics.Hall.Finite
import Mathlib.Combinatorics.Enumerative.DoubleCounting

namespace RegularMatchingDecomposition

private theorem perfect {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ) (pos : 0 < d)
    (R : V → Finset V) (row : ∀ p, (R p).card = d)
    (col : ∀ l, (Finset.univ.filter (fun p => l ∈ R p)).card = d) :
    ∃ e : V ≃ V, ∀ p, e p ∈ R p := by
  classical
  have hall (S : Finset V) : S.card ≤ (S.biUnion R).card := by
    let I := fun p l => l ∈ R p
    have lo (p) (hp : p ∈ S) : d ≤ ((S.biUnion R).bipartiteAbove I p).card := by
      rw [← row p]
      apply Finset.card_le_card
      intro l hl
      exact (Finset.mem_bipartiteAbove I).mpr ⟨Finset.mem_biUnion.mpr ⟨p,hp,hl⟩,hl⟩
    have hi (l) (_ : l ∈ S.biUnion R) : (S.bipartiteBelow I l).card ≤ d := by
      rw [← col l]
      apply Finset.card_le_card
      intro p hp
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,((Finset.mem_bipartiteBelow I).mp hp).2⟩
    exact Nat.le_of_mul_le_mul_right (Finset.card_mul_le_card_mul I lo hi) pos
  obtain ⟨f,inj,mem⟩ := (Finset.all_card_le_biUnion_card_iff_existsInjective' R).mp hall
  exact ⟨Equiv.ofBijective f ⟨inj,Finite.surjective_of_injective inj⟩,mem⟩

theorem finsets {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (R : V → Finset V) (row : ∀ p, (R p).card = d)
    (col : ∀ l, (Finset.univ.filter (fun p => l ∈ R p)).card = d) :
    ∃ M : Fin d → V ≃ V, (∀ p, Function.Injective (fun j => M j p)) ∧
      ∀ p l, l ∈ R p ↔ ∃ j, M j p = l := by
  classical
  induction d generalizing R with
  | zero =>
    refine ⟨Fin.elim0,fun _ x => Fin.elim0 x,?_⟩
    intro p l
    simp [Finset.card_eq_zero.mp (row p)]
  | succ d ih =>
    obtain ⟨e,em⟩ := perfect (d+1) (by omega) R row col
    let R' := fun p => (R p).erase (e p)
    have r' (p) : (R' p).card = d := by
      have h := Finset.card_erase_add_one (em p)
      change ((R p).erase (e p)).card = d
      rw [row] at h; omega
    have c' (l) : (Finset.univ.filter (fun p => l ∈ R' p)).card = d := by
      let S := Finset.univ.filter (fun p => l ∈ R p)
      have eq : Finset.univ.filter (fun p => l ∈ R' p) = S.erase (e.symm l) := by
        ext p
        simp only [R',S,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_erase]
        have equiv : l = e p ↔ p = e.symm l := by
          constructor
          · intro h; simp [h]
          · rintro rfl; simp
        tauto
      rw [eq]
      have hmem : e.symm l ∈ S := by
        apply Finset.mem_filter.mpr
        simpa using And.intro (Finset.mem_univ (e.symm l)) (em (e.symm l))
      have h := Finset.card_erase_add_one hmem
      have c : S.card = d+1 := col l
      omega
    obtain ⟨M,inj,covers⟩ := ih R' r' c'
    let full : Fin (d+1) → V ≃ V := Fin.cases e M
    have sep (p : V) (j : Fin d) : M j p ≠ e p :=
      (Finset.mem_erase.mp ((covers p (M j p)).mpr ⟨j,rfl⟩)).1
    refine ⟨full,?_,?_⟩
    · intro p i j h
      revert h
      refine Fin.cases ?_ (fun a => ?_) i <;> refine Fin.cases ?_ (fun b => ?_) j
      · exact fun _ => rfl
      · exact fun h => False.elim (sep p _ h.symm)
      · exact fun h => False.elim (sep p _ h)
      · exact fun h => congrArg Fin.succ (inj p h)
    · intro p l
      constructor
      · intro hit
        by_cases eq : l = e p
        · exact ⟨0,eq.symm⟩
        · obtain ⟨j,hj⟩ := (covers p l).mp (Finset.mem_erase.mpr ⟨eq,hit⟩)
          exact ⟨j.succ,hj⟩
      · rintro ⟨j,hj⟩
        revert hj
        refine Fin.cases ?_ (fun b => ?_) j
        · exact fun h => h ▸ em p
        · intro h
          exact (Finset.mem_erase.mp ((covers p l).mpr ⟨b,h⟩)).2

theorem decompose {V : Type*} [Fintype V] [DecidableEq V] (d : ℕ)
    (I : V → V → Prop) [DecidableRel I]
    (row : ∀ p, Fintype.card {l // I p l} = d)
    (col : ∀ l, Fintype.card {p // I p l} = d) :
    ∃ M : Fin d → V ≃ V, (∀ p, Function.Injective (fun j => M j p)) ∧
      ∀ p l, I p l ↔ ∃ j, M j p = l := by
  let R := fun p => Finset.univ.filter (I p)
  obtain ⟨M,inj,cover⟩ := finsets d R (fun p => by
    simpa [R,Fintype.card_subtype] using row p) (fun l => by
    simpa [R,Fintype.card_subtype] using col l)
  exact ⟨M,inj,fun p l => by simpa [R] using cover p l⟩

theorem inverse_injective {V J : Type*} (M : J → V ≃ V)
    (inj : ∀ p, Function.Injective (fun j => M j p)) (l : V) :
    Function.Injective (fun j => (M j).symm l) := by
  intro j k h
  change (M j).symm l = (M k).symm l at h
  apply inj ((M j).symm l)
  calc
    M j ((M j).symm l) = l := (M j).apply_symm_apply l
    _ = M k ((M j).symm l) := by rw [h,Equiv.apply_symm_apply]

theorem inverse_cover {V J : Type*} (I : V → V → Prop) (M : J → V ≃ V)
    (cover : ∀ p l, I p l ↔ ∃ j, M j p = l) (p l : V) :
    I p l ↔ ∃ j, (M j).symm l = p := by
  rw [cover]
  constructor
  · rintro ⟨j,e⟩; exact ⟨j,by rw [← e,Equiv.symm_apply_apply]⟩
  · rintro ⟨j,e⟩; exact ⟨j,by rw [← e,Equiv.apply_symm_apply]⟩

end RegularMatchingDecomposition
