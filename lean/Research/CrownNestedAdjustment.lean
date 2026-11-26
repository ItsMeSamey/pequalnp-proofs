import Research.CrownCircuitLabels
import Research.CrownCleanWeights
import Research.CrownNestDichotomy

namespace PEqualNP.Research.MissingCell.CrownLabels
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def twin (t : Fin 24) : Fin 24 := Fin.ofNat 24 (t.val+12)

private theorem ports : ∀ t : Fin 24,
    (t = rowPort (literalLabel t) ∧ twin t = colPort (literalLabel t)) ∨
    (t = colPort (literalLabel t) ∧ twin t = rowPort (literalLabel t)) := by decide

private theorem flip : ∀ t : Fin 24, twin (twin t) = t := by decide

private theorem sameLabel : ∀ a b : Fin 24, literalLabel a = literalLabel b → a=b ∨ a=twin b := by decide

private theorem bundle (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (noCollision : ∀ g h : Fin C.gates.length, g ≠ h → Disjoint (readAt C.gates 24 g.val) (readAt C.gates 24 h.val))
    (N : SingletonNest C) (aligned : N.b = twin N.a) (j : Fin 24) (hit : N.Contaminant j) :
    nestSig C j = {N.g,N.h} ∧ readAt C.gates 24 N.g.val = {N.a.val,j.val} ∧
    nestSig C (twin j) = ∅ := by
  obtain ⟨ra,rh⟩ := N.raw_readers hm rep mini size ors (noCollision _ _ N.order.ne)
  have cap : (nestSig C j).card ≤ 2 := by
    rw [nestSig,activeOrIds_card]
    exact literal_count_le_two C hm rep ors j
  have act := N.contaminant_signature hit rh cap
  have next : N.h ∈ nestSig C j := by rw [act]; simp
  have rg := nest_contaminated_first_readers C hm rep mini size ors N.a j hit.1.symm N.g N.h N.order ra hit.2 next cap
  refine ⟨act,rg,?_⟩
  have jb : j ≠ N.b := by
    intro e
    have gg := hit.2
    rw [e,N.late] at gg
    exact N.order.ne (Finset.mem_singleton.mp gg)
  have ta : twin j ≠ N.a := fun e => jb (by rw [aligned,←e,flip])
  have tb : twin j ≠ N.b := fun e => hit.1 (by rw [aligned] at e; simpa only [flip] using congrArg twin e)
  have tj : twin j ≠ j := (by decide : ∀ q : Fin 24, twin q ≠ q) j
  let U := A C (literalLabel j) ∪ B C (literalLabel j)
  have subs : nestSig C j ⊆ U ∧ nestSig C (twin j) ⊆ U := by
    rcases ports j with ⟨e,f⟩|⟨e,f⟩
    · exact ⟨(congrArg (nestSig C) e).symm ▸ (show nestSig C (rowPort (literalLabel j)) ⊆ U from Finset.subset_union_left),
        (congrArg (nestSig C) f).symm ▸ (show nestSig C (colPort (literalLabel j)) ⊆ U from Finset.subset_union_right)⟩
    · exact ⟨(congrArg (nestSig C) e).symm ▸ (show nestSig C (colPort (literalLabel j)) ⊆ U from Finset.subset_union_right),
        (congrArg (nestSig C) f).symm ▸ (show nestSig C (rowPort (literalLabel j)) ⊆ U from Finset.subset_union_left)⟩
  exact nest_bad_sibling_zero C N.a N.b j (twin j) N.g N.h N.order.ne rg rh ta tb tj U
    (union_cap C hm rep ors _) subs.1 subs.2

private def witness (C : Circuit) (i : L) : Prop :=
  ∃ N : SingletonNest C, N.b = twin N.a ∧ literalLabel N.a = i ∧ ∃ j, N.Contaminant j

private theorem oriented_clean (C : Circuit) (bad : Finset L) (t : Fin 24)
    (mem : t ∈ cleanPorts C bad) :
    literalLabel t ∉ bad ∧ ∃ N : SingletonNest C, N.a = t ∧ N.b = twin t := by
  have result (a b : Fin 24) (ea : a=t) (eb : b=twin t)
      (H : literalLabel t ∉ bad ∧ Early (sig C a) (sig C b)) :
      literalLabel t ∉ bad ∧ ∃ N : SingletonNest C, N.a = t ∧ N.b = twin t := by
    obtain ⟨hb,g,h,gh,active,late⟩ := H
    exact ⟨hb,⟨a,b,g,h,gh,active,late⟩,ea,eb⟩
  rcases ports t with ⟨e,f⟩|⟨e,f⟩
  · have info := (row_clean C bad (literalLabel t)).mp (e ▸ mem)
    exact result _ _ e.symm f.symm info
  · have info := (col_clean C bad (literalLabel t)).mp (e ▸ mem)
    exact result _ _ e.symm f.symm info

/-- For a minimum 12-crown circuit in the collision-free case, doubling every
clean early singleton preserves all wire capacities. The exceptional nested
labels inject into the labels with a silent singleton. -/
theorem nested_weight_adjustment (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C) (mini : crownSizeMinimal C)
    (size : C.size ≤ 40) (ors : (C.gates.filter isOrGate).length ≤ 23)
    (noCollision : ∀ g h : Fin C.gates.length, g ≠ h → Disjoint (readAt C.gates 24 g.val) (readAt C.gates 24 h.val)) :
    ∃ bad : Finset L, bad.card ≤ (silent C).card ∧ ∀ i,
      (C.wires (List.replicate 24 false)).getD i false = false →
      weightedWireMass C (fun t => (adjustedQuarter C bad t : ℚ)) i ≤ 4 := by
  classical
  let bad := Finset.univ.filter (witness C)
  have hbad (i : ↥bad) : witness C i.val := (Finset.mem_filter.mp i.property).2
  choose N hN using hbad
  choose j hj using (fun i => (hN i).2.2)
  have data (i : ↥bad) := bundle C hm rep mini size ors noCollision (N i) (hN i).1 (j i) (hj i)
  have silentTarget (i : ↥bad) : literalLabel (j i) ∈ silent C := by
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    have zero := (data i).2.2
    rcases ports (j i) with ⟨_,e⟩|⟨_,e⟩
    · exact Or.inr ((congrArg (nestSig C) e).symm.trans zero)
    · exact Or.inl ((congrArg (nestSig C) e).symm.trans zero)
  let map (i : ↥bad) : ↥(silent C) := ⟨_,silentTarget i⟩
  have inj : Function.Injective map := by
    intro u v he
    have eq : literalLabel (j u) = literalLabel (j v) := congrArg Subtype.val he
    rcases sameLabel _ _ eq with same|impossible
    · have act := (data v).1
      have read := (data v).2.1
      rw [← same] at act read
      have raw := (N u).same_contaminant (N v) (hj u) (data u).1 act (data u).2.1 read
      exact Subtype.ext ((hN u).2.1.symm.trans ((congrArg literalLabel raw).trans (hN v).2.1))
    · have live := (hj u).2
      rw [impossible,(data v).2.2] at live
      exact (Finset.notMem_empty _ live).elim
  refine ⟨bad,by simpa using Fintype.card_le_of_injective map inj,?_⟩
  intro i off
  apply clean_weighted_capacity C hm rep ors (cleanPorts C bad) twin _ _ i off
  · intro t ht q qt qb
    obtain ⟨nb,M,ma,mb⟩ := oriented_clean C bad t ht
    have aligned : M.b = twin M.a := by rw [ma,mb]
    have readers := M.raw_readers hm rep mini size ors (noCollision _ _ M.order.ne)
    have clean (p : Fin 24) (hit : M.g ∈ nestSig C p) : p = M.a := by
      by_contra ne
      apply nb
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_univ _,M,aligned,congrArg literalLabel ma,p,ne,hit⟩
    have dis := nest_clean_separate C M.a M.b M.g M.h M.early readers.2 clean q
      (by simpa only [ma] using qt) (by simpa only [mb] using qb)
    exact ma ▸ dis
  · intro t ht
    obtain ⟨_,M,ma,mb⟩ := oriented_clean C bad t ht
    rw [qsig]
    have e : sig C (twin t) = {M.h} := mb ▸ M.late
    rw [e,Finset.card_singleton]
    decide

end PEqualNP.Research.MissingCell.CrownLabels
