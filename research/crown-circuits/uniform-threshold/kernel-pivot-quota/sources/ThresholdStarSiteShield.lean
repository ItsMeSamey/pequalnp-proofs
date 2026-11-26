import ThresholdStarPrivateSite
import ThresholdStarShieldPhysical
import ThresholdStarProbeReadback
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction T2OrPartition
variable {C : Circuit} {n : Nat} {L : Layout C n} {u : Id C} {x : Fin n}

theorem PrivateSite.other_mem (P : PrivateSite L u x) :
    P.other ∈ (Block.meet (n+P.z.val) (L.left P.z) (L.right P.z)).exts := by
  have opp := P.partner
  cases s : P.side <;> simp [s] at opp <;> simp [Block.exts,←opp]

theorem PrivateSite.shield (P : PrivateSite L u x) (sel : Nat → Bool) (src f : Env)
    (blocked : run (n+u.val) sel true src (forest L Fin.val) f P.other=false) :
    Shielded (n+u.val) x.val (n+P.v.val) sel src (forest L Fin.val) f ∧
      ∀ b∈forest L Fin.val, OutsideTaps (n+u.val) (n+P.v.val) sel b := by
  apply physical_shield L x u P.v P.z (by rw [P.pair]) P.alone P.consumer sel src f _
    ⟨_,_,P.meet⟩
  intro l r recv
  have same : Block.meet (n+P.z.val) l r=.meet (n+P.z.val) (L.left P.z) (L.right P.z) :=
    List.inj_on_of_nodup_map (ThresholdFactorCut.output_nodup L Fin.val) recv P.meet rfl
  cases same
  have pin := P.pins
  have opp := P.partner
  have sep := P.separate
  cases s : P.side
  · simp only [s,Bool.false_eq_true,ite_false] at pin opp
    exact Or.inl ⟨pin,(by rwa [opp]),(by rwa [opp])⟩
  · simp only [s,ite_true] at pin opp
    exact Or.inr ⟨pin,(by rwa [opp]),(by rwa [opp])⟩

theorem PrivateSite.probe_stored (P : PrivateSite L u x) (bk : Book C n [] (forest L Fin.val)) :
    (n+P.v.val)∈outputs (forest L Fin.val) [] ∧ P.other∈outputs (forest L Fin.val) [] := by
  obtain ⟨p,t,mem,root⟩ := P.group
  exact ⟨root ▸ root_stored _ (.group p t) mem,external_stored _ _ bk _ P.meet _ P.other_mem⟩
#print axioms PrivateSite.shield
end ThresholdStarBypass
