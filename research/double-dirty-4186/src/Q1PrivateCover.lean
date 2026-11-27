import Q1PrivateCounts

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private

variable {V : Type*} [DecidableEq V]

def CoversOwned (p : ℕ → Bool → V) (k : ℕ) (S : Finset V) :=
  ∀ i < k, p i false ∈ S ∨ p i true ∈ S

private def chosen (p : ℕ → Bool → V) (k : ℕ) (t : ℕ → Bool) : Finset V :=
  (Finset.range k).image (fun i => p i (t i))

private theorem chosen_covers (p : ℕ → Bool → V) (k : ℕ) (t : ℕ → Bool) :
    CoversOwned p k (chosen p k t) := by
  intro i hi
  have mem : p i (t i) ∈ chosen p k t :=
    Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  cases eq : t i <;> simp_all

private theorem chosen_card (p : ℕ → Bool → V) (k : ℕ) (t : ℕ → Bool) :
    (chosen p k t).card ≤ k := by
  simpa only [chosen, Finset.card_range] using
    (Finset.card_image_le (s:=Finset.range k) (f:=fun i => p i (t i)))

def Saves (p : ℕ → Bool → V) (k : ℕ) (T : Finset V) :=
  ∃ S : Finset V, CoversOwned p k (T ∪ S) ∧ (T ∪ S).card < T.card+k

theorem covers_baseline (p : ℕ → Bool → V) (k : ℕ) (T : Finset V) :
    ∃ S : Finset V, CoversOwned p k (T ∪ S) ∧ (T ∪ S).card ≤ T.card+k := by
  let S := chosen p k (fun _ => false)
  refine ⟨S,?_,(Finset.card_union_le T S).trans (Nat.add_le_add_left (chosen_card ..) _)⟩
  intro i hi
  exact (chosen_covers p k _ i hi).imp (Finset.mem_union_right T) (Finset.mem_union_right T)

theorem saves_shared (p : ℕ → Bool → V) {k i j : ℕ} (T : Finset V)
    (hi : i < k) (hj : j < k) (ne : i ≠ j) (b d : Bool) (eq : p i b = p j d) :
    Saves p k T := by
  classical
  let t := fun z : ℕ => if z=i then b else d
  let S := chosen p k t
  have small : S.card < k := by
    have le : S.card ≤ k := chosen_card p k t
    by_contra! hn
    have card : ((Finset.range k).image (fun z => p z (t z))).card = (Finset.range k).card := by
      rw [Finset.card_range]; change S.card = k; omega
    exact ne ((Finset.card_image_iff.mp card) (Finset.mem_range.mpr hi) (Finset.mem_range.mpr hj)
      (by simpa [t, Ne.symm ne] using eq))
  refine ⟨S,?_,(Finset.card_union_le T S).trans_lt (Nat.add_lt_add_left small _)⟩
  intro z hz
  exact (chosen_covers p k t z hz).imp (Finset.mem_union_right T) (Finset.mem_union_right T)

theorem saves_precovered (p : ℕ → Bool → V) {k i : ℕ} (T : Finset V)
    (hi : i < k) (b : Bool) (mem : p i b ∈ T) : Saves p k T := by
  let S := chosen p k (fun _ => b)
  have memS : p i b ∈ S := Finset.mem_image.mpr ⟨i,Finset.mem_range.mpr hi,rfl⟩
  have overlap : 0 < (T ∩ S).card :=
    Finset.card_pos.mpr ⟨_,Finset.mem_inter.mpr ⟨mem,memS⟩⟩
  have sum := Finset.card_union_add_card_inter T S
  have le : S.card ≤ k := chosen_card .. 
  refine ⟨S,?_,by omega⟩
  intro z hz
  exact (chosen_covers p k (fun _ => b) z hz).imp (Finset.mem_union_right T) (Finset.mem_union_right T)

theorem covers_guard_pair (p : ℕ → Bool → V) {k : ℕ} (T L : Finset V) {u v : V}
    (eq : L={u,v}) (hit : CoversOwned p k L) :
    ∃ S : Finset V, CoversOwned p k (T ∪ S) ∧ (T ∪ S).card ≤ T.card+2 := by
  refine ⟨L,?_,(Finset.card_union_le T L).trans (Nat.add_le_add_left ?_ _)⟩
  · intro i hi
    exact (hit i hi).imp (Finset.mem_union_right T) (Finset.mem_union_right T)
  · rw [eq]; exact Finset.card_le_two

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Private
