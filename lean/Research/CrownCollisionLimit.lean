import Research.CrownSaturatedCollisions
import Research.CrownCollisionPath
import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def shareOrRead (C : Circuit) (i j : Fin C.gates.length) : Prop :=
  ∃ v ∈ readAt C.gates 24 i.val, v ∈ readAt C.gates 24 j.val

private theorem diag_separate (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (ors : (C.gates.filter isOrGate).length ≤ 23) (k : Fin 12)
    (active : (trueOrFlags C.gates (oneEach k k)).count true = 2) :
    let A := activeOrIds C.gates (oneEach k k)
    ∀ i ∉ A, ∀ j ∉ A, ∀ v ∈ readAt C.gates 24 i.val, v ∈ readAt C.gates 24 j.val → i = j := by
  dsimp only
  intro i hi j hj v vi vj
  by_contra ne
  exact Finset.disjoint_left.mp (crown_inactive_pair_disjoint C hm rep ors k active i j ne hi hj) vi vj

theorem crown_collision_limit (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (E : Finset (Finset (Fin C.gates.length)))
    (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧ shareOrRead C i j) :
    E.card ≤ 3 := by
  classical
  obtain ⟨k,_,act,_,_⟩ := crown_distinct_saturated_signatures C hm rep size ors
  let w := oneEach k k
  let A := activeOrIds C.gates w
  let P (i : Fin C.gates.length) := readAt C.gates 24 i.val
  let on (v : ℕ) : Prop := ((Circuit.mk C.gates 0).wires w).getD v false = true
  have hw : w.length = 24 := by simp [w,oneEach]
  have sig (i : Fin C.gates.length) : i ∈ A ↔ ∃ v ∈ P i, on v := by
    simpa only [A,P,on,← hw] using activeOrIds_iff_final_parent C.gates w i
  have card : A.card = 2 := (activeOrIds_card ..).trans act
  obtain ⟨a,b,_,eq⟩ := Finset.card_eq_two.mp card
  have sep := diag_separate C hm rep ors k act
  change (∀ i ∉ A, ∀ j ∉ A, ∀ v ∈ P i, v ∈ P j → i = j) at sep
  rw [eq] at sep
  apply CrownCollisions.saturated_collision_cap a b P on
    (fun i => readAt_card_le_two C.gates 24 i.val (fun g hg => (hm g hg).2)) _ _ sep E real
  · intro i hi
    exact (sig i).mp (eq ▸ hi)
  · intro i hi v hv val
    exact hi (eq ▸ (sig i).mpr ⟨v,hv,val⟩)

theorem crown_no_collision_path (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c d : Fin C.gates.length} (ab : shareOrRead C a b)
    (bc : shareOrRead C b c) (cd : shareOrRead C c d)
    (ac : a ≠ c) (ad : a ≠ d) (bd : b ≠ d) (bc_ne : b ≠ c)
    (ab_ne : a ≠ b) (cd_ne : c ≠ d) : False := by
  classical
  have forced (k : Fin 12) (act : (trueOrFlags C.gates (oneEach k k)).count true = 2) :
      activeOrIds C.gates (oneEach k k) = {b,c} := by
    let w := oneEach k k
    let A := activeOrIds C.gates w
    let P (i : Fin C.gates.length) := readAt C.gates 24 i.val
    let on (v : ℕ) : Prop := ((Circuit.mk C.gates 0).wires w).getD v false = true
    have hw : w.length = 24 := by simp [w,oneEach]
    have sig (i : Fin C.gates.length) : i ∈ A ↔ ∃ v ∈ P i, on v := by
      simpa only [A,P,on,← hw] using activeOrIds_iff_final_parent C.gates w i
    have card : A.card = 2 := (activeOrIds_card ..).trans act
    have sep := diag_separate C hm rep ors k act
    let edge (i j : Fin C.gates.length) := i ≠ j ∧ shareOrRead C i j
    apply CrownCollisions.path_forces_pair A (by omega) edge _ _ _
      ⟨ab_ne,ab⟩ ⟨bc_ne,bc⟩ ⟨cd_ne,cd⟩ ac ad bd bc_ne ab_ne cd_ne
    · rintro i j ⟨ne,v,vi,vj⟩
      exact ⟨ne.symm,v,vj,vi⟩
    · rintro i j ⟨ne,v,vi,vj⟩
      by_contra! hf
      exact ne (sep i hf.1 j hf.2 v vi vj)
    · intro i hi h hh j hj ih ij
      exact CrownCollisions.unique_quiet_neighbor A P on
        (fun i => readAt_card_le_two C.gates 24 i.val (fun g hg => (hm g hg).2))
        (fun i hi => (sig i).mp hi) (fun i hi v hv val => hi ((sig i).mpr ⟨v,hv,val⟩))
        sep hi hh hj ih.2 ij.2
  obtain ⟨k,j,hk,hj,ne⟩ := crown_distinct_saturated_signatures C hm rep size ors
  exact ne (flags_eq_of_ids_eq _ _ _ ((forced k hk).trans (forced j hj).symm))

end PEqualNP.Research.MissingCell
