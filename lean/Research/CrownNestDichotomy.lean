import Research.CrownNestedConsequences

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

abbrev nestSig (C : Circuit) (t : Fin 24) := activeOrIds C.gates (nestSingleton t)

structure SingletonNest (C : Circuit) where
  a : Fin 24
  b : Fin 24
  g : Fin C.gates.length
  h : Fin C.gates.length
  order : g < h
  early : nestSig C a = {g,h}
  late : nestSig C b = {h}

def SingletonNest.Contaminant {C : Circuit} (N : SingletonNest C) (j : Fin 24) :=
  j ≠ N.a ∧ N.g ∈ nestSig C j

private theorem fin_flag {C : Circuit} {t : Fin 24} (i : Nat)
    (hot : (trueOrFlags C.gates (nestSingleton t)).getD i false = true) : i < C.gates.length := by
  by_contra! bad
  rw [getD_missing (by rw [trueOrFlags_length]; omega :
    (trueOrFlags C.gates (nestSingleton t)).length ≤ i)] at hot
  contradiction

theorem SingletonNest.raw_readers {C : Circuit} (N : SingletonNest C) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (indep : Disjoint (readAt C.gates 24 N.g.val) (readAt C.gates 24 N.h.val)) :
    N.a.val ∈ readAt C.gates 24 N.g.val ∧ readAt C.gates 24 N.h.val = {N.b.val,24+N.g.val} := by
  have x (i : Nat) : (trueOrFlags C.gates (nestSingleton N.a)).getD i false = true ↔
      i = N.g.val ∨ i = N.h.val := by
    constructor
    · intro hi
      let k : Fin C.gates.length := ⟨i,fin_flag i hi⟩
      have hk : k ∈ nestSig C N.a := (activeOrIds_mem ..).mpr hi
      rw [N.early] at hk
      simpa [Fin.ext_iff,k] using hk
    · rintro (rfl|rfl)
      · exact (activeOrIds_mem ..).mp (show N.g ∈ nestSig C N.a by rw [N.early]; simp)
      · exact (activeOrIds_mem ..).mp (show N.h ∈ nestSig C N.a by rw [N.early]; simp)
  have y (i : Nat) : (trueOrFlags C.gates (nestSingleton N.b)).getD i false = true ↔ i = N.h.val := by
    constructor
    · intro hi
      let k : Fin C.gates.length := ⟨i,fin_flag i hi⟩
      have hk : k ∈ nestSig C N.b := (activeOrIds_mem ..).mpr hi
      rw [N.late] at hk
      exact congrArg Fin.val (Finset.mem_singleton.mp hk)
    · rintro rfl
      exact (activeOrIds_mem ..).mp (show N.h ∈ nestSig C N.b by rw [N.late]; simp)
  have gh := N.order
  refine ⟨nest_first_read C hm rep mini size ors _ (by simp [nestSingleton]) _ (nest_singleton_spec N.a)
    _ ((x _).mpr (Or.inl rfl)) ?_,nested_second_readers C hm rep mini size ors N.a N.b _ _
      (by simp [nestSingleton]) (by simp [nestSingleton]) (nest_singleton_spec _) (nest_singleton_spec _)
      _ _ gh x y indep⟩
  intro i hi
  cases e : (trueOrFlags C.gates (nestSingleton N.a)).getD i false with
  | false => rfl
  | true => have := (x _).mp e; omega

theorem SingletonNest.contaminant_signature {C : Circuit} (N : SingletonNest C) {j : Fin 24}
    (hj : N.Contaminant j) (lateReads : readAt C.gates 24 N.h.val = {N.b.val,24+N.g.val})
    (cap : (nestSig C j).card ≤ 2) : nestSig C j = {N.g,N.h} := by
  have gh := N.order.ne
  have g0 := (activeOrIds_mem ..).mp hj.2
  have hot := (nest_second_support C N.b N.g N.h (nestSingleton j) g0 lateReads j).mpr (Or.inr hj.2)
  apply (Finset.eq_of_subset_of_card_le _ (by simpa [gh] using cap)).symm
  intro k hk
  rcases Finset.mem_insert.mp hk with rfl|hk
  · exact hj.2
  · exact (Finset.mem_singleton.mp hk) ▸ hot

theorem SingletonNest.same_contaminant {C : Circuit} (M N : SingletonNest C) {j : Fin 24}
    (hm : M.Contaminant j)
    (mact : nestSig C j = {M.g,M.h}) (nact : nestSig C j = {N.g,N.h})
    (mr : readAt C.gates 24 M.g.val = {M.a.val,j.val})
    (nr : readAt C.gates 24 N.g.val = {N.a.val,j.val}) : M.a = N.a := by
  have eq := mact.symm.trans nact
  have gmem : M.g ∈ ({N.g,N.h} : Finset _) := eq ▸ Finset.mem_insert_self ..
  have hmem : M.h ∈ ({N.g,N.h} : Finset _) := eq ▸ Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have mlt := M.order
  have nlt := N.order
  simp only [Finset.mem_insert,Finset.mem_singleton,Fin.ext_iff] at gmem hmem
  have same : M.g.val = N.g.val := by omega
  have mem : M.a.val ∈ readAt C.gates 24 M.g.val := by rw [mr]; simp
  rw [same,nr] at mem
  rcases Finset.mem_insert.mp mem with e|e
  · exact Fin.ext e
  · exact (hm.1 (Fin.ext (Finset.mem_singleton.mp e).symm)).elim

end PEqualNP.Research.MissingCell
