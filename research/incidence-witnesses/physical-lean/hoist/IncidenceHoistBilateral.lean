import IncidenceHoistNormalize
import IncidenceHoistLive
namespace IncidenceHoistBilateral
open CircuitRewire IncidenceStartNormalization IncidenceHoistStage IncidenceHoistNormalize
open IncidenceHoistPrune

/-- Actual two-stage witnesses for the original scalar circuit. The two
census experiments must refer to these same live physical DAGs. -/
theorem stages {n : ℕ} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
    (hn : n=401^2+401+1) (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    (pos : flags C I) (neg : negatives C I n 401) :
    ∃ line both : Circuit n, LineStage I C line ∧ BilateralStage I line both ∧ Live line ∧ Live both := by
  obtain ⟨B,originalBudget,binB,liveB,_,_,posB,negB⟩ := source_live C I hn degree pos neg
  let L := transform B true
  let P := transform L false
  have binL : binary L := ops B true binB
  have posL : flags L I := positive B I negB posB true
  have negL : negatives L I n 401 := line_negative B I degree unique posB negB
  have andL : soleAnd L n := by
    intro i valid
    exact owner_private B I hn degree unique negB posB binB true ⟨i,valid⟩
  have liveL : Live L := IncidenceHoistLive.live B _ liveB
  refine ⟨L,P,⟨(budget B true).le.trans originalBudget,binL,posL,negL,andL⟩,
    ⟨(budget L false).le,ops L false binL,positive L I negL posL false,
     point_negative L I degree unique posL negL hn,?_,HoistPhysicalPorts.opposite_and_line L I negL andL,?_⟩,
    liveL,IncidenceHoistLive.live L _ liveL⟩
  · intro i valid one
    simp only [Nat.zero_add] at one ⊢
    exact owner_private L I hn degree unique negL posL binL false ⟨i,valid⟩ one
  · intro i valid
    exact HoistPhysicalPorts.opposite_uses L I negL false ⟨i,valid⟩

/-- The remaining two census estimates are applied to the retained physical
witnesses, so intermediate line multiplicities transfer to the final circuit. -/
theorem start_of_censuses {n : ℕ} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]
    (hn : n=401^2+401+1) (degree : ∀ l,Fintype.card {p // I p l}=401+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    (pos : flags C I) (neg : negatives C I n 401)
    (lineCount : ∀ L : Circuit n, LineStage I C L → Live L → soleCount L n≤3382)
    (pointCount : ∀ L P : Circuit n, LineStage I C L → BilateralStage I L P →
      Live L → Live P → soleCount P 0≤6461) :
    ∃ P : Circuit n, Live P ∧ P.size≤C.size ∧ flags P I ∧ negatives P I 3 3 ∧
      binary P ∧ soleAnd P 0 ∧ soleAnd P n ∧ soleCount P 0+soleCount P n≤9843 := by
  obtain ⟨L,P,l,p,liveL,liveP⟩ := stages C I hn degree unique pos neg
  exact ⟨P,liveP,round_start l p (lineCount L l liveL) (pointCount L P l p liveL liveP)⟩

#print axioms start_of_censuses
#print axioms stages
end IncidenceHoistBilateral
