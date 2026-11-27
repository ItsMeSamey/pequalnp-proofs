import SixD3OriginalProjection9822
import SixD3ClosedBoth9822
import SixWideOriginalThreeFour9822
namespace Research.Graph9822Profiles.OuterLive
open Research.Graph9822Resolution Research.Graph9822
open Research.Graph9822.ArbitraryScan Research.Graph9822.CommonBank
open PEqualNP.Outside.L_meta_9822.Sectors
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
theorem original_d3_excluded (gs : List DGate) (out : Nat) (size : gs.length≤17)
    (ok : WellWired gs 10) (ob : out<10+gs.length) (six : gs.countP Gate.isAnd=6)
    (computes : ∀ x : Fin 10 → Bool,(asCircuit gs out).eval (List.ofFn x)=edge x) :
    let cap := six.le
    let axis := switchAxis (switchAddrs gs 10) ((switchAddrs_length gs 10).trans_le cap)
    let p := ((gateEvents axis gs 10 ++ rawEvents 10).foldl paddedStep (initial out)).switches
    let R := tenR axis gs out
    let P := field p
    let d := ((Finset.univ : Finset (Fin 10)).filter (fun v => RayValue P (R v))).card
    d≠3 := by
  intro cap axis p R P d three
  obtain ⟨t,keep,A|B⟩ := original_d3_projection gs out size ok ob six computes three
  · exact (ThreeDirect.closedBoth keep).1 A
  · exact (ThreeDirect.closedBoth keep).2 B
theorem original_four (gs : List DGate) (out : Nat) (size : gs.length≤17)
    (ok : WellWired gs 10) (ob : out<10+gs.length) (six : gs.countP Gate.isAnd=6)
    (computes : ∀ x : Fin 10 → Bool,(asCircuit gs out).eval (List.ofFn x)=edge x) :
    let cap := six.le
    let axis := switchAxis (switchAddrs gs 10) ((switchAddrs_length gs 10).trans_le cap)
    let p := ((gateEvents axis gs 10 ++ rawEvents 10).foldl paddedStep (initial out)).switches
    let R := tenR axis gs out
    let P := field p
    let d := ((Finset.univ : Finset (Fin 10)).filter (fun v => RayValue P (R v))).card
    d=4 := by
  intro cap axis p R P d
  have range : d=3 ∨ d=4 := original_three_or_four gs out size ok ob six computes
  exact range.resolve_left (original_d3_excluded gs out size ok ob six computes)
end
end Research.Graph9822Profiles.OuterLive
#print axioms Research.Graph9822Profiles.OuterLive.original_d3_excluded
#print axioms Research.Graph9822Profiles.OuterLive.original_four
