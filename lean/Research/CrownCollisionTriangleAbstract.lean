import Research.CrownSaturatedCollisions

namespace CrownCollisions
variable {G : Type*} [DecidableEq G]

theorem collision_shape (a b : G) (E : Finset (Finset G)) (collide : G → G → Prop)
    (neighbor : ∀ g ∈ ({a,b} : Finset G), ∀ h ∉ ({a,b} : Finset G),
      ∀ k ∉ ({a,b} : Finset G), collide g h → collide g k → h = k)
    (classify : ∀ e ∈ E, e = {a,b} ∨ ∃ g ∈ ({a,b} : Finset G),
      ∃ h ∉ ({a,b} : Finset G), collide g h ∧ e = {g,h}) : ∃ c d, E ⊆ ({{a,b},{a,c},{b,d}} : Finset (Finset G)) := by
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
  exact ⟨f a, f b, sub⟩

end CrownCollisions

namespace CrownCollisions
variable {G : Type*} [DecidableEq G]
theorem triangle_of_shape {E : Finset (Finset G)} (q : E.card = 3)
    {a b c d : G} (shape : E ⊆ ({{a,b},{a,c},{b,d}} : Finset (Finset G)))
    (simple : ∀ e ∈ E, e.card = 2)
    (noPath : ∀ i j k l : G, i ≠ j → i ≠ k → i ≠ l → j ≠ k → j ≠ l → k ≠ l →
      ({i,j} : Finset G) ∈ E → ({j,k} : Finset G) ∈ E → ({k,l} : Finset G) ∈ E → False) :
    E = {{a,b},{a,c},{b,c}} := by
  have le (x y z : Finset G) : ({x,y,z} : Finset (Finset G)).card ≤ 3 := by
    have h := Finset.card_insert_le x (insert y {z})
    have k := Finset.card_insert_le y {z}
    simp only [Finset.card_singleton] at k
    omega
  have eq := Finset.eq_of_subset_of_card_le shape (by simpa [q] using le {a,b} {a,c} {b,d})
  have edges (x y : G) (h : ({x,y} : Finset G) ∈ E) : x ≠ y := by
    rintro rfl
    have := simple _ h
    simp at this
  have ab := edges a b (by rw [eq]; simp)
  have ac := edges a c (by rw [eq]; simp)
  have bd := edges b d (by rw [eq]; simp)
  have small (x y : Finset G) : ({x,y} : Finset (Finset G)).card ≤ 2 := by
    simpa only [Finset.card_singleton] using Finset.card_insert_le x {y}
  have bc : b ≠ c := by
    rintro rfl
    have z := small {a,b} {b,d}
    rw [eq] at q
    simp only [Finset.insert_idem] at q
    omega
  have ad : a ≠ d := by
    rintro rfl
    have z := small {a,b} {a,c}
    rw [eq] at q
    have dup : ({{a,b},{a,c},{b,a}} : Finset (Finset G)) = {{a,b},{a,c}} := by
      ext x
      simp only [Finset.mem_insert,Finset.mem_singleton]
      rw [Finset.pair_comm b a]
      tauto
    rw [dup] at q
    omega
  by_cases cd : c = d
  · simpa only [← cd] using eq
  · exact False.elim (noPath c a b d ac.symm bc.symm cd ab ad bd
      (by rw [eq,Finset.pair_comm c a]; simp) (by rw [eq]; simp) (by rw [eq]; simp))
end CrownCollisions

namespace CrownCollisions
variable {G W : Type*} [DecidableEq G] [DecidableEq W]
theorem saturated_collision_shape (a b : G) (P : G → Finset W) (on : W → Prop)
    (binary : ∀ g, (P g).card ≤ 2)
    (fires : ∀ g ∈ ({a,b} : Finset G), ∃ v ∈ P g, on v)
    (quiet : ∀ g ∉ ({a,b} : Finset G), ∀ v ∈ P g, ¬ on v)
    (separate : ∀ g ∉ ({a,b} : Finset G), ∀ h ∉ ({a,b} : Finset G),
      ∀ v ∈ P g, v ∈ P h → g = h)
    (E : Finset (Finset G)) (real : ∀ e ∈ E, ∃ i j, i ≠ j ∧ e = {i,j} ∧
      ∃ v ∈ P i, v ∈ P j) : ∃ c d, E ⊆ ({{a,b},{a,c},{b,d}} : Finset (Finset G)) := by
  classical
  apply collision_shape a b E (fun i j => ∃ v ∈ P i, v ∈ P j)
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
