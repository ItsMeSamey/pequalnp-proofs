import Research.CrownIndexedOrValues

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private theorem one_trigger_slot {G W I : Type*} [DecidableEq W]
    (P : G → Finset W) (binary : ∀ g, (P g).card ≤ 2)
    (first : I → G) (trigger : I → W) (tin : ∀ i, trigger i ∈ P (first i))
    (inj : Function.Injective trigger)
    (reserved : ∀ i, ∃ w ∈ P (first i), ∀ j, first j = first i → trigger j ≠ w) :
    Function.Injective first := by
  intro i j eq
  obtain ⟨w,hw,avoid⟩ := reserved i
  apply inj
  by_contra ne
  have ht := tin i
  have hu := eq ▸ tin j
  have aw := avoid i rfl
  have bw := avoid j eq.symm
  have sub : ({trigger i,trigger j,w} : Finset W) ⊆ P (first i) := by
    intro x hx
    simp only [Finset.mem_insert,Finset.mem_singleton] at hx
    rcases hx with rfl | rfl | rfl <;> assumption
  have h := Finset.card_le_card sub
  have big : ({trigger i,trigger j,w} : Finset W).card = 3 := by simp [ne,aw,bw]
  have cap := binary (first i)
  omega

private theorem first_below_last {I G : Type*} [Fintype I] [LinearOrder G]
    (E F : Finset G) (dis : Disjoint E F) (e2 : E.card = 2) (f2 : F.card = 2)
    (active : I → Finset G) (first : I → G) (inj : Function.Injective first)
    (shape : ∀ i, ∃ a ∈ E, ∃ b ∈ F, active i = {a,b})
    (on : ∀ i, first i ∈ active i)
    (before : ∀ i, ∀ g ∈ active i, first i ≤ g) : Fintype.card I ≤ 3 := by
  classical
  let T := E ∪ F
  have four : T.card = 4 := by simp [T,Finset.card_union_of_disjoint dis,e2,f2]
  have nonempty : T.Nonempty := Finset.card_pos.mp (by omega)
  let z := T.max' nonempty
  have inS (i : I) : first i ∈ T.erase z := by
    obtain ⟨a,ha,b,hb,pair⟩ := shape i
    have ab : a ≠ b := fun h => Finset.disjoint_left.mp dis ha (h ▸ hb)
    have am : a ∈ active i := by simp [pair]
    have bm : b ∈ active i := by simp [pair]
    have aT : a ∈ T := Finset.mem_union_left _ ha
    have bT : b ∈ T := Finset.mem_union_right _ hb
    have leA := before i a am
    have leB := before i b bm
    have ax : a ≤ z := Finset.le_max' T a aT
    have bx : b ≤ z := Finset.le_max' T b bT
    have fne : first i ≠ z := by
      intro hz
      rw [hz] at leA leB
      exact ab ((le_antisymm ax leA).trans (le_antisymm leB bx))
    apply Finset.mem_erase.mpr
    refine ⟨fne,?_⟩
    have hf := on i
    rw [pair] at hf
    rcases Finset.mem_insert.mp hf with eq | rest
    · exact eq ▸ aT
    · exact (Finset.mem_singleton.mp rest) ▸ bT
  let into (i : I) : T.erase z := ⟨first i,inS i⟩
  have bound := Fintype.card_le_of_injective into (fun i j eq => inj (congrArg Subtype.val eq))
  simpa [Finset.card_erase_of_mem (T.max'_mem nonempty),four,into,z] using bound

/-- Two disjoint, colliding pairs would give four endpoints. Every saturation
selects one endpoint of each pair, and the greatest endpoint can never fire
first. Each remaining endpoint has just one usable trigger slot. -/
theorem disjoint_collision_trigger_cap {I G W : Type*} [Fintype I] [LinearOrder G] [DecidableEq W]
    (E F : Finset G) (dis : Disjoint E F) (e2 : E.card = 2) (f2 : F.card = 2)
    (P : G → Finset W) (binary : ∀ g, (P g).card ≤ 2) (active : I → Finset G)
    (a2 : ∀ i, (active i).card = 2)
    (hitE : ∀ i, ∃ g ∈ E, g ∈ active i) (hitF : ∀ i, ∃ g ∈ F, g ∈ active i)
    (u v : W) (sharedE : ∀ g ∈ E, u ∈ P g) (sharedF : ∀ g ∈ F, v ∈ P g)
    (value : I → W → Bool) (fires : ∀ i g, (∃ x ∈ P g, value i x = true) → g ∈ active i)
    (first : I → G) (trigger : I → W) (inj : Function.Injective trigger)
    (on : ∀ i, first i ∈ active i) (before : ∀ i, ∀ g ∈ active i, first i ≤ g)
    (tin : ∀ i, trigger i ∈ P (first i)) (live : ∀ i, value i (trigger i) = true) :
    Fintype.card I ≤ 3 := by
  classical
  have shape (i : I) : ∃ a ∈ E, ∃ b ∈ F, active i = {a,b} := by
    obtain ⟨a,ae,ai⟩ := hitE i
    obtain ⟨b,bf,bi⟩ := hitF i
    have ab : a ≠ b := fun h => Finset.disjoint_left.mp dis ae (h ▸ bf)
    refine ⟨a,ae,b,bf,(Finset.eq_of_subset_of_card_le ?_ ?_).symm⟩
    · intro x hx
      rcases Finset.mem_insert.mp hx with eq | rest
      · exact eq ▸ ai
      · exact (Finset.mem_singleton.mp rest) ▸ bi
    · simp [a2,ab]
  have quiet {A B : Finset G} (D : Disjoint A B) (ca : A.card = 2)
      (x : W) (shared : ∀ g ∈ A, x ∈ P g) (hits : ∀ i, ∃ g ∈ B, g ∈ active i)
      (i : I) : value i x ≠ true := by
    intro h
    have sub : A ⊆ active i := fun g hg => fires i g ⟨x,shared g hg,h⟩
    have eq : A = active i := Finset.eq_of_subset_of_card_le sub (by simp [a2,ca])
    obtain ⟨g,bg,ag⟩ := hits i
    exact Finset.disjoint_left.mp D (eq ▸ ag) bg
  have reserve (i : I) : ∃ x ∈ P (first i), ∀ j, first j = first i → trigger j ≠ x := by
    obtain ⟨a,ae,b,bf,eq⟩ := shape i
    have fi := on i
    rw [eq] at fi
    rcases Finset.mem_insert.mp fi with fa | rest
    · refine ⟨u,sharedE _ (fa ▸ ae),fun j _ eqw => ?_⟩
      exact quiet dis e2 u sharedE hitF j (eqw ▸ live j)
    · have fb := Finset.mem_singleton.mp rest
      refine ⟨v,sharedF _ (fb ▸ bf),fun j _ eqw => ?_⟩
      exact quiet dis.symm f2 v sharedF hitE j (eqw ▸ live j)
  exact first_below_last E F dis e2 f2 active first (one_trigger_slot P binary first trigger tin inj reserve)
    shape on before

end PEqualNP.Research.MissingCell
