import Q1DoubleTopology
import Q1PureSupport

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open S4183 S4183.S98
attribute [local instance] gateOpDecEq

variable {n : ℕ} {C : Circuit} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]

/-- The mixer is the unique OR that must remain a special boundary wire. -/
def PlainWire (n : ℕ) (C : Circuit) (m w : ℕ) :=
  w < n ∨ ∃ k < C.gates.length, k ≠ m ∧ w = n+k ∧ (gateAt C k).op = GateOp.or

theorem plain_pin_semantics {m j w : ℕ} (D : DoubleDirty G C m) (ao : IsAO2 n C)
    (form : PEqualNP.TopForm.TopForm G C) (hj : j < C.gates.length)
    (andj : (gateAt C j).op = GateOp.and) (pin : w ∈ (gateAt C j).inputs)
    (plain : PlainWire n C m w) (x : Fin n → Bool) :
    W n C x w = true ↔ ∃ z ∈ orIn n C w, x z = true := by
  constructor
  · intro h
    obtain ⟨v,reach,hv,raw | ⟨k,hk,rfl,stop⟩⟩ := S90.or_trace (n := n) (C := C)
      (x := List.ofFn x) (by simp) w h
    · let z : Fin n := ⟨v,raw⟩
      exact ⟨z,S90.reach_mem_orIn z reach,by simpa only [← S90.val_ofFn C x z] using hv⟩
    · exfalso
      have hand := (ao.1 _ (S90.gateAt_mem hk)).resolve_right stop
      have bad : ¬BelowF G C k := fun hb => form k hk j hj hand hb andj
        (S90.operand_cone hj pin (ao.2.1 j hj w pin) reach)
      have dirty := (junk_iff G C k).mpr ⟨hk,hand,bad⟩
      rcases Relation.ReflTransGen.cases_tail reach with eq | ⟨v,before,last⟩
      · rcases plain with hi | ⟨k',_,_,hw,op⟩
        · omega
        · have kEq : k'=k := by omega
          subst k'
          exact stop op
      · obtain ⟨r,hr,ev,orr,read,_⟩ := last
        have rm := dirty_or_eq D ao dirty hr read orr
        subst r
        rw [ev] at before
        rcases Relation.ReflTransGen.cases_tail before with eq | ⟨_,_,last'⟩
        · rcases plain with hi | ⟨k',_,ne,hw,_⟩
          · omega
          · exact ne (by omega)
        · obtain ⟨r,hr,_,orr,read,_⟩ := last'
          exact no_mixer_or D ao hr read orr
  · rintro ⟨z,hz,hx⟩
    exact S90.reach_var_val x w z (S90.mem_orIn_reach z hz) hx

theorem plain_pin_anchor {m w : ℕ} (D : DoubleDirty G C m) (four : NoFourCycle G)
    (least : IsLeastAO G C) (plain : PlainWire n C m w) :
    (orIn n C w).card ≤ 1 ∨ Q1Pure.Anchored G C (orIn n C w) := by
  rcases plain with hw | ⟨k,hk,ne,rfl,op⟩
  · exact Or.inl (orIn_input C w hw)
  by_cases small : (orIn n C (n+k)).card ≤ 1
  · exact Or.inl small
  obtain ⟨z,hz⟩ := Finset.card_pos.mp (show 0 < (orIn n C (n+k)).card by omega)
  have hn : ¬BelowF G C k := by
    intro hb
    have yes := S90.reach_var_val (pairInput z z) (n+k) z (S90.mem_orIn_reach z hz) (S90.pairInput_left z z)
    exact G.loopless.irrefl z ((S90.graphFun_pair G z z).mp (hb _ yes))
  apply Or.inr
  apply Q1Pure.lambda_anchor four least
  by_contra hl
  have hN : k ∈ orN G C := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,op,hn⟩
  have mem := Finset.mem_sdiff.mpr ⟨hN,hl⟩
  exact ne (by simpa only [D.exception,Finset.mem_singleton] using mem)

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
