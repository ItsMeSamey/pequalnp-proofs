import ThresholdUpperCycleDecode
namespace ThresholdUpperCatalogue
variable {V : Type*} [LinearOrder V]

/-- The matching specified by the opposite of the least vertex. This is the
two-edge complement of the correspondingly named four-cycle inside K₄. -/
noncomputable def matching (Q : Finset V) (d : V) : Finset (Finset V) :=
  let c := anchor Q d
  {{c,d},(Q.erase c).erase d}

private theorem concrete_cycle (c a b d : V) (Q : Finset V)
    (all : Q={c,a,b,d}) (ac : a≠c) (bc : b≠c) (dc : d≠c)
    (ab : a≠b) (ad : a≠d) (bd : b≠d) (root : anchor Q d=c) :
    cycle (⟨Q,d⟩ : CycleName V) = {{c,a},{c,b},{d,a},{d,b}} := by
  classical
  simp only [cycle,root]
  simp [all,spokes,ac,bc,dc,ab,ad,bd,Ne.symm ac,Ne.symm bc,Ne.symm dc,
    Ne.symm ab,Ne.symm ad,Ne.symm bd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.insert_comm,Finset.pair_comm]

  ext e
  simp only [Finset.mem_insert,Finset.mem_singleton]
  tauto

theorem two_matchings_cycle (Q : Finset V) (sz : Q.card=4) (a b d : V)
    (ha : a∈opposites Q) (hb : b∈opposites Q) (hd : d∈opposites Q)
    (ab : a≠b) (ad : a≠d) (bd : b≠d) :
    matching Q a ∪ matching Q b = cycle (⟨Q,d⟩ : CycleName V) := by
  classical
  have non : Q.Nonempty := Finset.card_pos.mp (by omega)
  let c := Q.min' non
  have hc : c∈Q := Q.min'_mem non
  have mem (x : V) (h : x∈opposites Q) : x≠c ∧ x∈Q :=
    Finset.mem_erase.mp (show x∈Q.erase c by simpa [opposites,non,c] using h)
  obtain ⟨ac,aq⟩ := mem a ha
  obtain ⟨bc,bq⟩ := mem b hb
  obtain ⟨dc,dq⟩ := mem d hd
  have all : Q={c,a,b,d} := by
    symm
    apply Finset.eq_of_subset_of_card_le
    · intro x hx
      simp only [Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl <;> assumption
    · simp [sz,ac.symm,bc.symm,dc.symm,ab,ad,bd]
  have anc (j : V) : anchor Q j=c := by simp [anchor,non,c]
  rw [concrete_cycle c a b d Q all ac bc dc ab ad bd (anc d)]
  simp only [matching,anc]
  simp [all,ac,bc,dc,ab,ad,bd,Ne.symm ac,Ne.symm bc,Ne.symm dc,
    Ne.symm ab,Ne.symm ad,Ne.symm bd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.insert_comm,Finset.pair_comm]

/-- If m matching names survive on a four-set, every pair forces a distinct
cycle name. In particular retaining one costs at most the present cycles. -/
theorem four_loss (Q : Finset V) (sz : Q.card=4) (R : Finset (Finset V)) :
    ((opposites Q).filter (fun d => matching Q d⊆R)).card ≤
    1+((opposites Q).filter (fun d => cycle (⟨Q,d⟩ : CycleName V)⊆R)).card := by
  classical
  have non : Q.Nonempty := Finset.card_pos.mp (by omega)
  have three : (opposites Q).card=3 := by
    simp [opposites,non,Finset.card_erase_of_mem (Q.min'_mem non),sz]
  obtain ⟨a,b,d,ab,ad,bd,h⟩ := Finset.card_eq_three.mp three
  have ha : a∈opposites Q := by simp [h]
  have hb : b∈opposites Q := by simp [h]
  have hd : d∈opposites Q := by simp [h]
  let ok := fun i => matching Q i⊆R
  let cy := fun i => cycle (⟨Q,i⟩ : CycleName V)⊆R
  have ca : ok b → ok d → cy a := fun x y => by
    unfold cy; rw [←two_matchings_cycle Q sz b d a hb hd ha bd ab.symm ad.symm]
    exact Finset.union_subset x y
  have cb : ok a → ok d → cy b := fun x y => by
    unfold cy; rw [←two_matchings_cycle Q sz a d b ha hd hb ad ab bd.symm]
    exact Finset.union_subset x y
  have cd : ok a → ok b → cy d := fun x y => by
    unfold cy; rw [←two_matchings_cycle Q sz a b d ha hb hd ab ad bd]
    exact Finset.union_subset x y
  change ((opposites Q).filter ok).card ≤ 1+((opposites Q).filter cy).card
  rw [h]
  by_cases oa : ok a <;> by_cases ob : ok b <;> by_cases od : ok d <;>
    by_cases ya : cy a <;> by_cases yb : cy b <;> by_cases yd : cy d <;>
    simp_all [Finset.filter_insert,Finset.filter_singleton,ab,ad,bd] <;> omega
end ThresholdUpperCatalogue
