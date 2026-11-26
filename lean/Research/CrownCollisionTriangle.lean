import Research.CrownCollisionLimit
import Research.CrownCollisionTriangleAbstract

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

private theorem crown_collision_container (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (E : Finset (Finset (Fin C.gates.length)))
    (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧ shareOrRead C i j) :
    ∃ a b c d, E ⊆ ({{a,b},{a,c},{b,d}} : Finset (Finset (Fin C.gates.length))) := by
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
  have sep (i : Fin C.gates.length) (hi : i ∉ A) (j : Fin C.gates.length) (hj : j ∉ A)
      (v : ℕ) (vi : v ∈ P i) (vj : v ∈ P j) : i = j := by
    by_contra ne
    exact Finset.disjoint_left.mp (crown_inactive_pair_disjoint C hm rep ors k act i j ne hi hj) vi vj
  change (∀ i ∉ A, ∀ j ∉ A, ∀ v ∈ P i, v ∈ P j → i = j) at sep
  rw [eq] at sep
  refine ⟨a,b,?_⟩
  apply CrownCollisions.saturated_collision_shape a b P on
    (fun i => readAt_card_le_two C.gates 24 i.val (fun g hg => (hm g hg).2)) _ _ sep E real
  · intro i hi
    exact (sig i).mp (eq ▸ hi)
  · intro i hi v hv val
    exact hi (eq ▸ (sig i).mpr ⟨v,hv,val⟩)

/-- Three actual collision edges force a triangle. -/
theorem crown_collision_triangle (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (E : Finset (Finset (Fin C.gates.length)))
    (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧ shareOrRead C i j)
    (card : E.card = 3) : ∃ a b c, E = {{a,b},{a,c},{b,c}} := by
  classical
  obtain ⟨a,b,c,d,shape⟩ := crown_collision_container C hm rep size ors E real
  refine ⟨a,b,c,CrownCollisions.triangle_of_shape card shape ?_ ?_⟩
  · intro e he
    obtain ⟨i,j,ij,rfl,_⟩ := real e he
    simp [ij]
  · have phys (i j : Fin C.gates.length) (ij : i ≠ j) (h : ({i,j} : Finset _) ∈ E) :
        shareOrRead C i j := by
      obtain ⟨x,y,_,eq,v,vx,vy⟩ := real _ h
      have hi : i ∈ ({x,y} : Finset _) := eq ▸ Finset.mem_insert_self ..
      have hj : j ∈ ({x,y} : Finset _) := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self j)
      simp only [Finset.mem_insert, Finset.mem_singleton] at hi hj
      rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> first
        | exact ⟨v,vx,vy⟩
        | exact ⟨v,vy,vx⟩
        | exact (ij rfl).elim
    intro i j k l ij ik il jk jl kl e₁ e₂ e₃
    exact crown_no_collision_path C hm rep size ors (phys i j ij e₁) (phys j k jk e₂)
      (phys k l kl e₃) ik il jl jk ij kl

end PEqualNP.Research.MissingCell
