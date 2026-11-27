import Q1DoubleTopology

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

abbrev MixerRoute (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ) :=
  Q0Partition.EndsAt (fun i j => (i = m ∨ i ∈ junk G C) ∧ j ∈ readers n C i)
    (fun i => i ∈ centreless G C)

theorem affected_exists {m : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) : ∃ t ∈ centreless G C, MixerRoute n G C m m t := by
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun A hA agree =>
    least.2.2 A (IsAO2_of_AO n A hA) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_, hout⟩ := least_out n C hL
    (by obtain ⟨x,hx⟩ := gf_true n G edge; exact ⟨x,(hf x).trans hx⟩)
    (by intro u; obtain ⟨x,hu,hx⟩ := gf_var n G u; exact ⟨x,hu,(hf x).trans hx⟩)
  have walk (d : ℕ) : ∀ i, C.gates.length-i=d → m ≤ i → (i=m ∨ i ∈ junk G C) →
      ∃ t ∈ centreless G C, MixerRoute n G C m i t := by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hdi mi hi
      have facts : i<C.gates.length ∧ ¬BelowF G C i ∧ orIn n C (n+i) = ∅ := by
        rcases hi with rfl | hj
        · exact ⟨(mixer_info D).1,(mixer_info D).2.2,mixer_empty D least.1⟩
        · obtain ⟨hl,hand,hbad⟩ := (S4183.junk_iff G C i).mp hj
          exact ⟨hl,hbad,Q0.and_empty_support hand⟩
      obtain ⟨hir,hbad,hempty⟩ := facts
      have hnout : n+i ≠ C.output := by
        intro he
        apply hbad
        intro x hx
        change W n C x (n+i) = true at hx
        rw [he] at hx
        exact (hf x).symm.trans hx
      obtain ⟨r,hir',hr,hin⟩ := least_read n C hL hout i (by omega)
      have rd : r ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hin⟩
      have nonterm : i ∉ centreless G C := fun h =>
        hbad (Finset.mem_filter.mp ((Finset.mem_filter.mp h).1 : i ∈ tops G C)).2.2
      have hand : (gateAt C r).op = GateOp.and := by
        apply (least.1.1 _ (S4183.S90.gateAt_mem hr)).resolve_right
        intro hor
        rcases hi with rfl | hj
        · exact no_mixer_or D least.1 hr hin hor
        · have eq := dirty_or_eq D least.1 hj hr hin hor
          omega
      by_cases hb : BelowF G C r
      · have ht : r ∈ tops G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hand,hb⟩
        have hc : r ∈ centreless G C := by
          apply Finset.mem_filter.mpr
          refine ⟨ht,?_⟩
          rcases Q0.reader_pin least.1 hr hin with eq | eq
          · exact Or.inl (by simpa [side,eq] using hempty)
          · exact Or.inr (by simpa [side,eq] using hempty)
        exact ⟨r,hc,.next nonterm ⟨hi,rd⟩ (.stop hc)⟩
      · have hj := (S4183.junk_iff G C r).mpr ⟨hr,hand,hb⟩
        obtain ⟨t,ht,tail⟩ := ih (C.gates.length-r) (by omega) r rfl (by omega) (.inr hj)
        exact ⟨t,ht,.next nonterm ⟨hi,rd⟩ tail⟩
  exact walk _ m rfl (by omega) (.inl rfl)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
