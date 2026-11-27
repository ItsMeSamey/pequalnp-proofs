import Q1Degree

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure

theorem collapse_residual_fork {n : ℕ} (R : Finset (Sym2 (Fin n))) (E : Finset (Fin n))
    (h u v : Fin n) (hu : s(h,u) ∈ R) (hv : s(h,v) ∈ R)
    (shape : E = {u,v})
    (meets : ∀ a b, s(a,b) ∈ R → a ∈ E ∨ b ∈ E)
    (noFork : ∀ a ∈ E, ∀ b c, s(a,b) ∈ R → s(a,c) ∈ R → b = c) :
    R = {s(h,u),s(h,v)} := by
  classical
  have uh : s(u,h) ∈ R := by rw [Sym2.eq_swap]; exact hu
  have vh : s(v,h) ∈ R := by rw [Sym2.eq_swap]; exact hv
  have oriented (a b : Fin n) (ab : s(a,b) ∈ R) (ae : a ∈ E) :
      s(a,b) ∈ ({s(h,u),s(h,v)} : Finset _) := by
    have bh := noFork a ae b h ab
    rw [shape] at ae
    simp only [Finset.mem_insert, Finset.mem_singleton] at ae
    rcases ae with rfl | rfl
    · have e := bh uh
      rw [e, Sym2.eq_swap]
      exact Finset.mem_insert_self _ _
    · have e := bh vh
      apply Finset.mem_insert_of_mem
      apply Finset.mem_singleton.mpr
      rw [e]
      exact Sym2.eq_swap
  ext e
  constructor
  · induction e using Sym2.inductionOn with
    | _ a b =>
      intro ab
      rcases meets a b ab with ae | be
      · exact oriented a b ab ae
      · have ba : s(b,a) ∈ R := Sym2.eq_swap (a := a) (b := b) ▸ ab
        exact Sym2.eq_swap (a := b) (b := a) ▸ oriented b a ba be
  · intro he
    simp only [Finset.mem_insert, Finset.mem_singleton] at he
    rcases he with rfl | rfl
    · exact hu
    · exact hv

theorem fork_cover_cost {n : ℕ} {R : Finset (Sym2 (Fin n))} {h u v : Fin n}
    (shape : R = {s(h,u),s(h,v)}) (uv : u ≠ v) (d : ℕ) (hd : 0 < d) :
    (∀ a b, s(a,b) ∈ R → a ∈ ({h} : Finset _) ∨ b ∈ ({h} : Finset _)) ∧
    ({h} : Finset _).card + R.card = 3 ∧ 3 ≤ d + 2 := by
  classical
  have neq : s(h,u) ≠ s(h,v) := fun e => uv (Sym2.congr_right.mp e)
  subst R
  constructor
  · intro a b he
    simp only [Finset.mem_insert, Finset.mem_singleton, Sym2.eq_iff] at he
    simp only [Finset.mem_singleton]
    tauto
  · simp [neq] <;> omega

open PEqualNP.TopForm PEqualNP.CircuitLowerBounds
open PEqualNP.Outside.L_meta_4186_aux.Q0

theorem fork_of_shape {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {clauses : Finset (Finset (Fin n))} {E : Finset (Fin n)}
    (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    (clean : ∀ x y, hitsPair clauses x y → G.Adj x y)
    (R : Finset (Sym2 (Fin n)))
    (capture : ∀ a b, s(a,b) ∈ R → hitsPair clauses a b ∧ s(a,b) ∈ Ustar G C)
    (h u v : Fin n) (uv : u ≠ v) (ru : s(h,u) ∈ R) (rv : s(h,v) ∈ R)
    (shape : E = {u,v}) : R = {s(h,u),s(h,v)} := by
  obtain ⟨hu,hu'⟩ := capture h u ru
  obtain ⟨hv,hv'⟩ := capture h v rv
  have mem := (degree_exception four anchor clean hu hv hu' hv' uv).1
  apply collapse_residual_fork R E h u v ru rv shape
  · intro a b ab
    exact (capture a b ab).1 E mem
  · intro a ha b c ab ac
    by_contra bc
    obtain ⟨hitB,resB⟩ := capture a b ab
    obtain ⟨hitC,resC⟩ := capture a c ac
    exact (degree_exception four anchor clean hitB hitC resB resC bc).2.1 ha

theorem fork_of_children {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    {clauses : Finset (Finset (Fin n))} {E A B : Finset (Fin n)}
    (four : NoFourCycle G) (anchor : clauseStars G C (clauses.erase E))
    (clean : ∀ x y, hitsPair clauses x y → G.Adj x y)
    (split : E = A ∪ B) (children : clauseStars G C {A,B})
    (R : Finset (Sym2 (Fin n)))
    (capture : ∀ a b, s(a,b) ∈ R → hitsPair clauses a b ∧ s(a,b) ∈ Ustar G C)
    (h u v : Fin n) (uv : u ≠ v) (ru : s(h,u) ∈ R) (rv : s(h,v) ∈ R) :
    R = {s(h,u),s(h,v)} := by
  obtain ⟨hu,hu'⟩ := capture h u ru
  obtain ⟨hv,hv'⟩ := capture h v rv
  exact fork_of_shape four anchor clean R capture h u v uv ru rv
    (degree_children four anchor clean hu hv hu' hv' uv split children).1

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
