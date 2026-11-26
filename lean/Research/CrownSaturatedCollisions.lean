import Mathlib.Data.Finset.Card

namespace CrownCollisions

variable {G W : Type*} [DecidableEq G] [DecidableEq W]

omit [DecidableEq G] in
/-- A firing binary OR can share a predecessor with at most one of the quiet ORs
if their predecessor sets are disjoint. -/
theorem unique_quiet_neighbor (A : Finset G) (P : G → Finset W) (on : W → Prop)
    (binary : ∀ g, (P g).card ≤ 2)
    (fires : ∀ g ∈ A, ∃ v ∈ P g, on v)
    (quiet : ∀ g ∉ A, ∀ v ∈ P g, ¬ on v)
    (separate : ∀ g ∉ A, ∀ h ∉ A, ∀ v ∈ P g, v ∈ P h → g = h)
    {g h k : G} (hg : g ∈ A) (hh : h ∉ A) (hk : k ∉ A)
    (gh : ∃ v ∈ P g, v ∈ P h) (gk : ∃ v ∈ P g, v ∈ P k) : h = k := by
  obtain ⟨u,hu,live⟩ := fires g hg
  obtain ⟨v,hv,hvh⟩ := gh
  obtain ⟨w,hw,hwk⟩ := gk
  have uv : u ≠ v := fun e => quiet h hh v hvh (e ▸ live)
  have uw : u ≠ w := fun e => quiet k hk w hwk (e ▸ live)
  have vw : v = w := by
    by_contra ne
    have sub : ({u,v,w} : Finset W) ⊆ P g := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      rcases hx with rfl | rfl | rfl <;> assumption
    have size := Finset.card_le_card sub
    have three : ({u,v,w} : Finset W).card = 3 := by simp [uv,uw,ne]
    have := binary g
    omega
  exact separate h hh k hk v hvh (vw ▸ hwk)

theorem collision_count (a b : G) (E : Finset (Finset G)) (collide : G → G → Prop)
    (neighbor : ∀ g ∈ ({a,b} : Finset G), ∀ h ∉ ({a,b} : Finset G),
      ∀ k ∉ ({a,b} : Finset G), collide g h → collide g k → h = k)
    (classify : ∀ e ∈ E, e = {a,b} ∨ ∃ g ∈ ({a,b} : Finset G),
      ∃ h ∉ ({a,b} : Finset G), collide g h ∧ e = {g,h}) : E.card ≤ 3 := by
  classical
  let f (g : G) := if H : ∃ h ∉ ({a,b} : Finset G), collide g h then H.choose else g
  let S : Finset (Finset G) := {{a,b},{a,f a},{b,f b}}
  have sub : E ⊆ S := by
    intro e he
    rcases classify e he with rfl | ⟨g,hg,h,hh,gh,rfl⟩
    · simp [S]
    · have ex : ∃ k ∉ ({a,b} : Finset G), collide g k := ⟨h,hh,gh⟩
      have eq : h = f g := by
        simp only [f,dite_eq_left ex]
        exact neighbor g hg h hh _ ex.choose_spec.1 gh ex.choose_spec.2
      rw [eq]
      rcases Finset.mem_insert.mp hg with rfl | hg
      · simp [S]
      · obtain rfl := Finset.mem_singleton.mp hg
        simp [S]
  have h := Finset.card_le_card sub
  have lim : S.card ≤ 3 := by
    unfold S
    have h₁ := Finset.card_insert_le ({a,b} : Finset G) ({ {a,f a}, {b,f b} } : Finset (Finset G))
    have h₂ := Finset.card_insert_le ({a,f a} : Finset G) ({ {b,f b} } : Finset (Finset G))
    simp only [Finset.card_singleton] at h₂
    omega
  omega
/-- A saturated diagonal with two live ORs permits at most three unordered
pairs of distinct OR gates that share a predecessor. -/
theorem saturated_collision_cap (a b : G) (P : G → Finset W) (on : W → Prop)
    (binary : ∀ g, (P g).card ≤ 2)
    (fires : ∀ g ∈ ({a,b} : Finset G), ∃ v ∈ P g, on v)
    (quiet : ∀ g ∉ ({a,b} : Finset G), ∀ v ∈ P g, ¬ on v)
    (separate : ∀ g ∉ ({a,b} : Finset G), ∀ h ∉ ({a,b} : Finset G),
      ∀ v ∈ P g, v ∈ P h → g = h)
    (E : Finset (Finset G)) (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧
      ∃ v ∈ P i, v ∈ P j) : E.card ≤ 3 := by
  classical
  apply collision_count a b E (fun i j => ∃ v ∈ P i, v ∈ P j)
  · intro g hg h hh k hk gh gk
    exact unique_quiet_neighbor _ P on binary fires quiet separate hg hh hk gh gk
  intro e he
  obtain ⟨i,j,ij,rfl,v,vi,vj⟩ := real e he
  by_cases hi : i ∈ ({a,b} : Finset G) <;> by_cases hj : j ∈ ({a,b} : Finset G)
  · left
    simp only [Finset.mem_insert,Finset.mem_singleton] at hi hj
    rcases hi with rfl | rfl <;> rcases hj with rfl | rfl <;> simp_all [Finset.pair_comm]
  · exact Or.inr ⟨i,hi,j,hj,⟨v,vi,vj⟩,rfl⟩
  · exact Or.inr ⟨j,hj,i,hi,⟨v,vj,vi⟩,Finset.pair_comm ..⟩
  · exact (ij (separate i hi j hj v vi vj)).elim

end CrownCollisions
