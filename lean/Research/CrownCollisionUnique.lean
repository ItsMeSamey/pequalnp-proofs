import Research.CrownNoTriangle
import Research.CrownNoAdjacentCollision
import Research.CrownCollisionsMeet

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem crown_collision_unique (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    {a b c d : Fin C.gates.length} (ab : a ≠ b) (cd : c ≠ d)
    (p : shareOrRead C a b) (q : shareOrRead C c d) :
    ({a,b} : Finset _) = {c,d} := by
  classical
  have sym {i j : Fin C.gates.length} (h : shareOrRead C i j) : shareOrRead C j i := by
    obtain ⟨v,vi,vj⟩ := h
    exact ⟨v,vj,vi⟩
  have nd {i j : Fin C.gates.length} (h : shareOrRead C i j) :
      ¬ Disjoint (readAt C.gates 24 i.val) (readAt C.gates 24 j.val) := by
    obtain ⟨v,vi,vj⟩ := h
    exact fun dis => Finset.disjoint_left.mp dis vi vj
  have same {x y z : Fin C.gates.length} (xy : x ≠ y) (yz : y ≠ z)
      (u : shareOrRead C x y) (v : shareOrRead C y z) : x = z := by
    by_contra xz
    by_cases w : shareOrRead C x z
    · exact crown_no_triangle_collision C hm rep size ors xy yz xz u v w
    · exact crown_no_adjacent_nontriangle C hm rep size ors xz xy yz u v w
  have meet := crown_collisions_meet C hm rep size ors a b c d ab cd (nd p) (nd q)
  obtain ⟨x,hx,hy⟩ := Finset.not_disjoint_iff.mp meet
  simp only [Finset.mem_insert,Finset.mem_singleton] at hx hy
  rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
  · rw [same ab.symm cd (sym p) q]
  · rw [same ab.symm cd.symm (sym p) (sym q),Finset.pair_comm]
  · rw [same ab cd p q,Finset.pair_comm]
  · rw [same ab cd.symm p (sym q)]

theorem crown_collision_count_le_one (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (E : Finset (Finset (Fin C.gates.length)))
    (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧ shareOrRead C i j) :
    E.card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro e he f hf
  obtain ⟨a,b,ab,rfl,p⟩ := real e he
  obtain ⟨c,d,cd,rfl,q⟩ := real f hf
  exact crown_collision_unique C hm rep size ors ab cd p q

end PEqualNP.Research.MissingCell
