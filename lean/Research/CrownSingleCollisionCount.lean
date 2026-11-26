import Research.CrownIndexedOrReads

namespace PEqualNP.Research.MissingCell

/-- A family of distinct two-element sets with just one possible intersecting
pair contributes at least twice its cardinality minus one distinct wires. -/
theorem single_collision_wire_count {G W : Type*} [DecidableEq G] [DecidableEq W]
    (S : Finset G) (P : G → Finset W)
    (two : ∀ g ∈ S, (P g).card = 2)
    (distinct : ∀ g ∈ S, ∀ h ∈ S, g ≠ h → P g ≠ P h)
    (unique : ∀ g ∈ S, ∀ h ∈ S, ∀ j ∈ S, ∀ k ∈ S, g ≠ h → j ≠ k →
      ¬ Disjoint (P g) (P h) → ¬ Disjoint (P j) (P k) → ({g,h} : Finset G) = {j,k}) :
    2 * S.card ≤ (S.biUnion P).card + 1 := by
  classical
  have sum2 (T : Finset G) (sub : T ⊆ S) (sep : (T : Set G).PairwiseDisjoint P) :
      (T.biUnion P).card = 2*T.card := by
    rw [Finset.card_biUnion sep]
    calc
      ∑ g ∈ T, (P g).card = ∑ _g ∈ T, 2 :=
        Finset.sum_congr rfl (fun g hg => two g (sub hg))
      _ = _ := by simp [Nat.mul_comm]
  by_cases sep : (S : Set G).PairwiseDisjoint P
  · rw [sum2 S (fun _ h => h) sep]
    omega
  · change ¬ (∀ g ∈ S, ∀ h ∈ S, g ≠ h → Disjoint (P g) (P h)) at sep
    push Not at sep
    obtain ⟨g,gs,h,hs,gh,hit⟩ := sep
    let T := S.erase g
    have sub : T ⊆ S := Finset.erase_subset ..
    have split (j : G) (jm : j ∈ T) (k : G) (km : k ∈ T) (jk : j ≠ k) : Disjoint (P j) (P k) := by
      by_contra collide
      have pair := unique g gs h hs j (sub jm) k (sub km) gh jk hit collide
      have gm : g ∈ ({j,k} : Finset G) := pair ▸ Finset.mem_insert_self g {h}
      simp only [Finset.mem_insert,Finset.mem_singleton] at gm
      exact gm.elim (fun e => (Finset.mem_erase.mp jm).1 e.symm)
        (fun e => (Finset.mem_erase.mp km).1 e.symm)
    have tsize := sum2 T sub (fun j jm k km jk => split j jm k km jk)
    have notsub : ¬ P g ⊆ P h := by
      intro le
      exact distinct g gs h hs gh (Finset.eq_of_subset_of_card_le le (by rw [two g gs,two h hs]))
    obtain ⟨w,wg,wh⟩ := Finset.not_subset.mp notsub
    have wfresh : w ∉ T.biUnion P := by
      intro wr
      obtain ⟨k,km,wk⟩ := Finset.mem_biUnion.mp wr
      have kg := (Finset.mem_erase.mp km).1
      have col : ¬ Disjoint (P g) (P k) := fun dis => Finset.disjoint_left.mp dis wg wk
      have eq := unique g gs h hs g gs k (sub km) gh kg.symm hit col
      have kh : k ∈ ({g,h} : Finset G) := eq ▸ (Finset.mem_insert_of_mem (Finset.mem_singleton_self k))
      rcases Finset.mem_insert.mp kh with eqg | eqh
      · exact kg eqg
      · exact wh ((Finset.mem_singleton.mp eqh) ▸ wk)
    have unionSub : insert w (T.biUnion P) ⊆ S.biUnion P := by
      apply Finset.insert_subset (Finset.mem_biUnion.mpr ⟨g,gs,wg⟩)
      intro x hx
      obtain ⟨j,jm,xj⟩ := Finset.mem_biUnion.mp hx
      exact Finset.mem_biUnion.mpr ⟨j,sub jm,xj⟩
    have card := Finset.card_le_card unionSub
    rw [Finset.card_insert_of_notMem wfresh,tsize] at card
    have diff : T.card+1 = S.card := Finset.card_erase_add_one gs
    omega

end PEqualNP.Research.MissingCell
