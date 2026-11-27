import Q1PureBase
import Q0Routes

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Pure
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q0ReaderDeps S4183.S98

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}

theorem clean_dirty_reader_centreless (hAO : IsAO2 n C)
    (hq : NoDirtyOr G C) {j r : ℕ}
    (hj : j ∈ junk G C) (hr : r < C.gates.length)
    (hin : n+j ∈ (gateAt C r).inputs) (hclean : BelowF G C r) :
    r ∈ centreless G C := by
  have hnot := hq hj hr hin
  have hand := (hAO.1 _ (Q0ReaderDeps.S90.gateAt_mem hr)).resolve_right hnot
  have ht : r ∈ tops G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hand, hclean⟩
  have hjand : (gateAt C j).op = GateOp.and := (Finset.mem_filter.mp hj).2.1
  have empty := and_empty_support (n := n) hjand
  apply Finset.mem_filter.mpr
  refine ⟨ht, ?_⟩
  rcases reader_pin hAO hr hin with e | e
  · exact Or.inl (by simpa [side, e] using empty)
  · exact Or.inr (by simpa [side, e] using empty)

theorem some_dirty_route (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (hq : NoDirtyOr G C) (g : ℕ) (hg : g ∈ junk G C) :
    ∃ t ∈ centreless G C, DirtyRoute n G C g t := by
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun D hD agree =>
    least.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_, hout⟩ := least_out n C hL
    (by obtain ⟨x, hx⟩ := gf_true n G edge; exact ⟨x, (hf x).trans hx⟩)
    (by intro u; obtain ⟨x, hu, hx⟩ := gf_var n G u; exact ⟨x, hu, (hf x).trans hx⟩)
  have walk (d : ℕ) : ∀ i, C.gates.length - i = d → i ∈ junk G C →
      ∃ t ∈ centreless G C, DirtyRoute n G C i t := by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro i hdi hi
      obtain ⟨hir, _, hbad⟩ := (S4183.junk_iff G C i).mp hi
      have hnout : n+i ≠ C.output := by
        intro he
        apply hbad
        intro x hx
        change W n C x (n+i) = true at hx
        rw [he] at hx
        exact (hf x).symm.trans hx
      obtain ⟨r, hir', hr, hin⟩ := least_read n C hL hout i (by omega)
      have hreader : r ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr, hin⟩
      have hnterminal : i ∉ centreless G C := by
        intro hc
        have ht : i ∈ tops G C := (Finset.mem_filter.mp hc).1
        exact hbad (Finset.mem_filter.mp ht).2.2
      by_cases hb : BelowF G C r
      · have hc := clean_dirty_reader_centreless least.1 hq hi hr hin hb
        exact ⟨r, hc, .next hnterminal ⟨hi, hreader⟩ (.stop hc)⟩
      · have ha := (least.1.1 _ (Q0ReaderDeps.S90.gateAt_mem hr)).resolve_right
          (hq hi hr hin)
        have hj := (S4183.junk_iff G C r).mpr ⟨hr, ha, hb⟩
        obtain ⟨t, ht, tail⟩ := ih (C.gates.length-r) (by omega) r rfl hj
        exact ⟨t, ht, .next hnterminal ⟨hi, hreader⟩ tail⟩
  exact walk _ g rfl hg

end PEqualNP.Outside.L_meta_4186_aux.Q1Pure
