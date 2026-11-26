import Research.CrownTightState
import Research.CrownCrossMass

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge TightStep

/-- For a cold wire extending outside a tight block, the shared singletons
can be counted twice without exceeding unit capacity. -/
theorem tight_block_crossing (n : ℕ) (gs : List Gate) (hm : Monotone2 (Circuit.mk gs 0))
    (b h : ℕ) (tb : tightWire n gs b)
    (hc : ((Circuit.mk gs 0).wires (List.replicate n false)).getD h false = false)
    (outside : ¬wireSupport (n:=n) gs h ⊆ wireSupport gs b) :
    overlapMass (singletonWeight (Circuit.mk gs 0)) (wireSupport (n:=n) gs h) (wireSupport gs b) ≤ 1 := by
  induction gs using List.reverseRecOn generalizing b h with
  | nil =>
    have dis : Disjoint (wireSupport (n:=n) [] h) (wireSupport [] b) := by
      apply Finset.disjoint_left.mpr
      intro i ih ib
      have raw (j : ℕ) (x : i ∈ wireSupport [] j) : j = i.val := by
        have hh := (Finset.mem_filter.mp x).2
        change (singleInput i).getD j false = true at hh
        by_cases valid : j<n
        · have e : (singleInput i).getD j false = decide ((⟨j,valid⟩ : Fin n) = i) := by
            simp only [singleInput,List.getD_eq_getElem?_getD,List.getElem?_ofFn,dite_eq_left valid,Option.getD_some]
          exact congrArg Fin.val (of_decide_eq_true (e.symm.trans hh))
        · rw [getD_missing (by simp [singleInput];omega)] at hh; contradiction
      exact outside (by rw [(raw h ih).trans (raw b ib).symm])
    rw [overlapMass,Finset.disjoint_iff_inter_eq_empty.mp dis,Finset.sum_empty,add_zero]
    exact singleton_weight_capacity (Circuit.mk [] 0) hm h hc
  | append_singleton gs g ih =>
    let B := wireSupport (n:=n) (gs++[g]) b
    let H := wireSupport (n:=n) (gs++[g]) h
    let old := singletonWeight (n:=n) (Circuit.mk gs 0)
    let now := singletonWeight (n:=n) (Circuit.mk (gs++[g]) 0)
    have hm' : Monotone2 (Circuit.mk gs 0) := fun k hk => hm k (List.mem_append_left _ hk)
    have op := (hm g (by simp)).1
    have desc := transfer gs g hm' op b tb
    change B = cut n gs g ∨ _ at desc
    change ¬ H ⊆ B at outside
    change overlapMass now H B ≤ 1
    have wle (i : Fin n) : now i ≤ old i := by
      change singletonWeight _ i ≤ singletonWeight _ i
      rw [next_weight]
      split <;> linarith [weight_positive gs i]
    have old_bound (p : ℕ)
        (cold : ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false)
        (ext : ¬ wireSupport (n:=n) gs p ⊆ B) :
        overlapMass now (wireSupport (n:=n) gs p) B ≤ 1 := by
      rcases desc with eb | ⟨q,tq,eq,_⟩
      · have weights : now = fun i => if i ∈ cut n gs g then old i / 2 else old i :=
          funext (next_weight gs g)
        rw [eb,weights,overlap_discount_eq]
        exact singleton_weight_capacity (Circuit.mk gs 0) hm' p cold
      · change B = wireSupport (n:=n) gs q at eq
        rw [eq] at ext ⊢
        exact (overlap_mass_mono_weights _ _ wle).trans (ih hm' q p tq cold ext)
    have nh := next_support (n:=n) gs g h
    change H = _ at nh
    rw [next_val,List.length_replicate] at hc
    by_cases idx : h=n+gs.length
    · rw [ite_eq_left idx] at hc nh
      rcases op with hand|hor
      · obtain ⟨p,hp,cold⟩ : ∃ p ∈ g.inputs, ((Circuit.mk gs 0).wires (List.replicate n false)).getD p false = false := by
          simpa [gateBool,hand,GateOp.eval] using hc
        have sub : H ⊆ wireSupport (n:=n) gs p := by
          intro i hi
          rw [nh] at hi
          have all : ∀ j ∈ g.inputs, ((Circuit.mk gs 0).wires (singleInput i)).getD j false = true := by
            simpa [gateBool,hand,GateOp.eval] using (Finset.mem_filter.mp hi).2
          exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,all p hp⟩
        exact (overlap_mass_mono_set B now (fun i => (weight_positive _ i).le) sub).trans
          (old_bound p cold (fun subs => outside (sub.trans subs)))
      · change g.op = .or at hor
        have cutH : H = cut n gs g := nh.trans (by ext; simp [cut,freshSupport,isOrGate,hor])
        rcases desc with eb|⟨q,_,eq,dis⟩
        · exact False.elim (outside ((cutH.trans eb.symm).le))
        · change B = wireSupport (n:=n) gs q at eq
          have no : Disjoint H B := eq ▸ cutH ▸ dis.symm
          rw [overlapMass,Finset.disjoint_iff_inter_eq_empty.mp no,Finset.sum_empty,add_zero]
          apply singleton_weight_capacity (Circuit.mk (gs++[g]) 0) hm h
          rw [next_val,List.length_replicate,ite_eq_left idx]; exact hc
    · rw [ite_eq_right idx] at hc nh
      exact nh ▸ old_bound h hc (nh ▸ outside)
end PEqualNP.Research.MissingCell
