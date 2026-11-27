import Q1DoubleTopology
import Q1PureFactor

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98

open PEqualNP.MetaComplexity PEqualNP.EdgeOwnership

def OutsideArms (n : ℕ) (C : Circuit) (g m : ℕ) : Prop :=
  ∀ w ∈ (gateAt C m).inputs, ¬ AndPath n C g w

private theorem outside_rules {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g : ℕ) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) {m : ℕ} (D : DoubleDirty G C m) (outside : OutsideArms n C g m)
    (hg : g ∈ junk G C) : PinRules G C g := by
  classical
  obtain ⟨reader, out, _⟩ := main_real n G C edge least form
  have clean {i j : ℕ} (hi : i < C.gates.length) (hb : BelowF G C i)
      (hj : j < C.gates.length) (pin : n+i ∈ (gateAt C j).inputs) : j ∈ orT G C := by
    have hr : j ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, pin⟩
    have ne : n+i ≠ C.output := by
      intro e
      have ix : C.output-n = i := by omega
      rw [ix] at out
      simpa [out] using hr
    obtain ⟨r, singleton, hop, below⟩ := reader i hi hb ne
    rw [singleton, Finset.mem_singleton] at hr
    subst r
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj, hop, below⟩
  constructor
  · intro j hj hn w hw i hi eq
    obtain ⟨hl, _, hb⟩ := Finset.mem_filter.mp hi
    exact hn (clean (Finset.mem_range.mp hl) hb hj (eq ▸ hw))
  · intro j hj hn hor w hw path
    have ends : ∃ i, w = n+i ∧ i < C.gates.length ∧ (gateAt C i).op = .and := by
      cases path with
      | source =>
        obtain ⟨bound, op, _⟩ := (S4183.junk_iff G C g).mp hg
        exact ⟨g,rfl,bound,op⟩
      | step _ bound op _ => exact ⟨_,rfl,bound,op⟩
    obtain ⟨i, rfl, bound, op⟩ := ends
    by_cases hb : BelowF G C i
    · exact hn (clean bound hb hj hw)
    · have eq := dirty_or_eq D least.1 ((S4183.junk_iff G C i).mpr ⟨bound,op,hb⟩) hj hw hor
      subst j
      exact outside _ hw path

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

private theorem outside_top {m g : ℕ} (D : DoubleDirty G C m) (outside : OutsideArms n C g m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (hg : g ∈ junk G C) :
    ∃ t ∈ tops G C, affected n C g t = true := by
  classical
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun A hA agree =>
    least.2.2 A (IsAO2_of_AO n A hA) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_, hout⟩ := least_out n C hL
    (by obtain ⟨x,hx⟩ := gf_true n G edge; exact ⟨x,(hf x).trans hx⟩)
    (by intro u; obtain ⟨x,hu,hx⟩ := gf_var n G u; exact ⟨x,hu,(hf x).trans hx⟩)
  have walk (k : ℕ) : ∀ i, C.gates.length-i=k → i ∈ junk G C → AndPath n C g (n+i) →
      ∃ t ∈ tops G C, affected n C g t = true := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hik hi path
      obtain ⟨hir,_,hbad⟩ := (S4183.junk_iff G C i).mp hi
      have hnout : n+i ≠ C.output := by
        intro he
        apply hbad
        intro x hx
        change W n C x (n+i) = true at hx
        rw [he] at hx
        exact (hf x).symm.trans hx
      obtain ⟨r,hir',hr,hin⟩ := least_read n C hL hout i (by omega)
      have hand : (gateAt C r).op = .and := by
        apply (least.1.1 _ (S4183.S90.gateAt_mem hr)).resolve_right
        intro hor
        have eq := dirty_or_eq D least.1 hi hr hin hor
        subst r
        exact outside _ hin path
      have reach := AndPath.step path hr hand hin
      by_cases hb : BelowF G C r
      · exact ⟨r, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hand,hb⟩,
          by simpa [affected] using reach⟩
      · exact ih (C.gates.length-r) (by omega) r rfl ((S4183.junk_iff G C r).mpr ⟨hr,hand,hb⟩) reach
  exact walk _ g rfl hg .source

theorem external_only_single_reader {m g : ℕ} (D : DoubleDirty G C m) (outside : OutsideArms n C g m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C)
    (hg : g ∈ junk G C) : (readers n C g).card ≤ 1 := by
  by_contra! two
  obtain ⟨src,sem⟩ := top_wire_semantics G C g least.1 hg (outside_rules G C g edge least form D outside hg)
  obtain ⟨A,ao,same,short⟩ := actual_competitor G C g
    (Q1Pure.row_savings_unconditional least.1 hg) (by omega) (by
      intro B good
      have dirty := ((S4183.junk_iff G C g).mp hg).2.2
      exact join_from_top_slots G C g edge least form dirty (affected n C g) _ B (src B good)
        (outside_top D outside edge least hg) (fun t _ => read_good good (n+t)) sem)
  exact (Nat.not_le_of_gt short) (least.2.2 A ao same)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
