import Research.CrownTightState

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge TightStep

private theorem two_cover_tight {I J : Type*} [DecidableEq I] [DecidableEq J]
    (S : Finset I) (D : Finset J) (P : J → Finset I) (wt : I → ℚ)
    (pos : ∀ i, 0 ≤ wt i) (cap : ∀ j ∈ D, (∑ i ∈ P j, wt i) ≤ 1)
    (len : D.card ≤ 2) (full : (∑ i ∈ S, wt i) = 2)
    (cover : ∀ i ∈ S, ∃ j ∈ D, i ∈ P j) (j : J) (hj : j ∈ D) :
    (∑ i ∈ P j, wt i) = 1 := by
  classical
  have each (i) (hi : i ∈ S) : wt i ≤ ∑ j ∈ D, if i ∈ P j then wt i else 0 := by
    obtain ⟨p,hp,ip⟩ := cover i hi
    simpa only [ite_eq_left ip] using
      (Finset.single_le_sum (s:=D) (f:=fun j => if i ∈ P j then wt i else 0)
        (fun j _ => by split <;> simp [pos]) hp)
  have bound : 2 ≤ ∑ j ∈ D, ∑ i ∈ P j, wt i := by
    calc
      _ = ∑ i ∈ S, wt i := full.symm
      _ ≤ ∑ i ∈ S, ∑ j ∈ D, if i ∈ P j then wt i else 0 := Finset.sum_le_sum each
      _ = ∑ j ∈ D, ∑ i ∈ S, if i ∈ P j then wt i else 0 := Finset.sum_comm
      _ ≤ _ := by
        apply Finset.sum_le_sum
        intro k _
        rw [←Finset.sum_filter]
        exact Finset.sum_le_sum_of_subset_of_nonneg
          (fun i hi => (Finset.mem_filter.mp hi).2) (fun i _ _ => pos i)
  refine le_antisymm (cap j hj) ?_
  by_contra! small
  have low := Finset.sum_lt_sum (s:=D) cap ⟨j,hj,small⟩
  simp only [Finset.sum_const,nsmul_eq_mul,mul_one] at low
  have sz : (D.card : ℚ) ≤ 2 := by exact_mod_cast len
  linarith

theorem tight_wire_pure (n : ℕ) (gs : List Gate) (hm : Monotone2 (Circuit.mk gs 0))
    (a : ℕ) (ht : tightWire n gs a) (y : List Bool) (ly : y.length=n) :
    ((Circuit.mk gs 0).wires y).getD a false = true ↔
      ∃ i ∈ wireSupport (n:=n) gs a, y.getD i.val false = true := by
  constructor
  · induction gs using List.reverseRecOn generalizing a with
    | nil =>
      intro hot
      change y.getD a false = true at hot
      have valid : a < n := by
        by_contra! h
        rw [getD_missing (by omega)] at hot
        contradiction
      let i : Fin n := ⟨a,valid⟩
      refine ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,hot⟩
      change (singleInput i).getD a false = true
      simp only [singleInput,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left valid,Option.getD_some]
      exact decide_eq_true rfl
    | append_singleton gs g ih =>
      intro hot
      have hm' : Monotone2 (Circuit.mk gs 0) := fun k hk => hm k (List.mem_append_left _ hk)
      obtain ⟨off,full⟩ := ht
      rw [next_val,List.length_replicate] at off
      rw [next_val,ly] at hot
      rw [next_support] at full ⊢
      by_cases idx : a=n+gs.length
      · rw [ite_eq_left idx] at off hot full ⊢
        obtain ⟨hop,fan⟩ := hm g (by simp)
        rcases hop with ha|ho
        · have ex : ∃ p ∈ g.inputs, ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false := by
            simpa [gateBool,ha,GateOp.eval] using off
          obtain ⟨p,hp,cold⟩ := ex
          have sub : freshSupport (n:=n) gs g ⊆ wireSupport gs p := by
            intro i hi
            have all : ∀ j ∈ g.inputs, ((Circuit.mk gs 0).wires (singleInput i)).getD j false = true := by
              simpa [gateBool,ha,GateOp.eval] using (Finset.mem_filter.mp hi).2
            exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,all p hp⟩
          have none : cut n gs g = ∅ := by ext; simp [cut,isOrGate,ha]
          simp only [next_weight,none,Finset.notMem_empty,ite_false] at full
          obtain ⟨eq,mass⟩ := tight_subset_rigidity _ _ _ (weight_positive gs) sub full
            (singleton_weight_capacity (Circuit.mk gs 0) hm' p cold)
          have all : ∀ j ∈ g.inputs, ((Circuit.mk gs 0).wires y).getD j false = true := by
            simpa [gateBool,ha,GateOp.eval] using hot
          rw [eq]
          exact ih hm' p ⟨cold,mass⟩ (all p hp)
        · change g.op = .or at ho
          let D := g.inputs.toFinset
          let S := freshSupport (n:=n) gs g
          let wt := singletonWeight (n:=n) (Circuit.mk gs 0)
          have cutS : cut n gs g = S := by ext; simp [S,cut,freshSupport,isOrGate,ho]
          have raw : (∑ i ∈ S, wt i) = 2 := by
            have eq : (∑ i ∈ S, singletonWeight (Circuit.mk (gs++[g]) 0) i) = (∑ i ∈ S, wt i)/2 := by
              rw [div_eq_mul_inv,Finset.sum_mul]
              apply Finset.sum_congr rfl
              intro i hi
              rw [next_weight,cutS,ite_eq_left hi,div_eq_mul_inv]
            change (∑ i ∈ S, _) = 1 at full
            linarith
          have cold (p) (hp : p ∈ D) : ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false := by
            have all : ∀ p ∈ g.inputs, ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false := by
              simpa [gateBool,ho,GateOp.eval] using off
            exact all p (List.mem_toFinset.mp hp)
          have member (i : Fin n) : i ∈ S ↔ ∃ p ∈ D, i ∈ wireSupport gs p := by
            simp [S,D,freshSupport,wireSupport,gateBool,ho,GateOp.eval]
          obtain ⟨p,hp,on⟩ : ∃ p ∈ g.inputs, ((Circuit.mk gs 0).wires y).getD p false = true := by
            simpa [gateBool,ho,GateOp.eval] using hot
          have pd := List.mem_toFinset.mpr hp
          have pm := two_cover_tight S D (wireSupport (n:=n) gs) wt (fun i => (weight_positive gs i).le)
            (fun j hj => singleton_weight_capacity (Circuit.mk gs 0) hm' j (cold j hj))
            ((List.toFinset_card_le _).trans fan) raw (fun i hi => (member i).mp hi) p pd
          obtain ⟨i,ip,iy⟩ := ih hm' p ⟨cold p pd,pm⟩ on
          exact ⟨i,(member i).mpr ⟨p,pd,ip⟩,iy⟩
      · rw [ite_eq_right idx] at hot off full ⊢
        simp only [next_weight] at full
        obtain ⟨_,mass⟩ := tight_discount_rigidity _ _ _ (weight_positive gs)
          (singleton_weight_capacity (Circuit.mk gs 0) hm' a off) full
        exact ih hm' a ⟨off,mass⟩ hot
  · rintro ⟨i,hi,iy⟩
    let C := Circuit.mk gs a
    apply eval_mono_live C n (singleInput i) y hm (by simp [singleInput]) ly _ (Finset.mem_filter.mp hi).2
    intro k _ hot
    by_cases valid : k<n
    · have e : (singleInput i).getD k false = decide ((⟨k,valid⟩ : Fin n) = i) := by
        simp only [singleInput,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left valid,Option.getD_some]
      have eq := congrArg Fin.val (of_decide_eq_true (e.symm.trans hot))
      change k=i.val at eq
      rw [eq]; exact iy
    · rw [getD_missing (by simp [singleInput];omega)] at hot; contradiction
end PEqualNP.Research.MissingCell
