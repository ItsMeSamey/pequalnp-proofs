import ThresholdStarColdPhysical
import ThresholdLeakPins
import ThresholdSharpEndpoint
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence
open ThresholdSharedPartition ThresholdSharedFlow T2OrPartition

theorem regular_star_boundary : ThresholdSharpEndpoint.StarBoundary := by
  classical
  intro n hn gs out M reg u hub L
  let C := source gs out
  let S := singleAt L u
  change S.card≤1+max (fan L u) (leak L u)
  have hu : u∈ThresholdSharedOrBudget.sharedOrs C n := by simpa [hubs] using hub
  have center : L.op u=.or := (physical_op L u).mp (List.mem_filter.mp hu).2
  have shared := (List.mem_filter.mp (List.mem_filter.mp hu).1).2
  have big : 2≤fan L u := by simpa [fan_readers] using shared
  by_cases small : S.card≤2
  · omega
  have simple := classified_simple (by omega : 2≤n) M reg
  let P := fun a:S => Classical.choice (private_site L M u a.val a.property (simple.1 a.val))
  have structure' := cold_structure M reg u hub simple.1 simple.2.1 S (by omega) P
  let own := fun a:S => ((P a).z,(P a).side)
  let charge := fun a:S => ThresholdLeakPins.opposite (own a)
  let hot := fun a:S => on L u (P a).other=true
  let W := (Finset.univ : Finset S).filter hot
  let F := (Finset.univ : Finset S).filter (fun a => ¬hot a)
  have spent (a:S) : ThresholdLeakPins.source L (own a)=n+(P a).v.val := (P a).pins
  have other (a:S) : ThresholdLeakPins.source L (charge a)=(P a).other := by
    have eq := (P a).partner
    cases h : (P a).side <;> simpa [ThresholdLeakPins.source,ThresholdLeakPins.opposite,own,charge,h] using eq
  have tag (a:S) : L.op (P a).z=.and := by
    have physical := (P a).consumer
    have lk := gate_lookup (L.atIndex (P a).z)
    have gate : C.gates.get (P a).z=binary (L.op (P a).z) (L.left (P a).z) (L.right (P a).z) := by simpa using lk
    rw [gate] at physical
    cases h : L.op (P a).z <;> simp_all [binary,gateOp]
  have leakHit (a:S) (ha : a∈W) : charge a∈ThresholdLeakPins.leakPins L u := by
    have ph : on L u (ThresholdLeakPins.source L (charge a))=true := by rw [other]; exact (Finset.mem_filter.mp ha).2
    have neq : (P a).z≠u := by intro e; have t := tag a; rw [e,center] at t; contradiction
    have cold := structure'.1 a
    change on L u (n+(P a).v.val)=false at cold
    have seen : on L u (ThresholdLeakPins.source L (own a))=false := by rwa [spent]
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,tag a,?_,ph⟩
    change active L u (P a).z=false
    rw [row_eq,if_neg neq,tag]
    cases h : (P a).side <;> simp [ThresholdLeakPins.source,own,h] at seen <;> simp [seen]
  have unique : Function.Injective charge := by
    intro a b same
    have pp : own a=own b := by
      simpa only [charge,ThresholdLeakPins.opposite_opposite] using congrArg ThresholdLeakPins.opposite same
    have wire := congrArg (ThresholdLeakPins.source L) pp
    rw [spent,spent] at wire
    have vv : (P a).v=(P b).v := Fin.ext (Nat.add_left_cancel wire)
    apply Subtype.ext
    apply simple.2.1
    rw [(P a).pair,(P b).pair,vv]
  have warm : W.card ≤ leak L u := by
    rw [←ThresholdLeakPins.card_leakPins]
    exact Finset.card_le_card_of_injOn charge leakHit (fun _ _ _ _ e => unique e)
  have cool : F.card≤1 := by
    apply Finset.card_le_one.mpr
    intro a ha b hb
    have ca : ¬hot a := (Finset.mem_filter.mp ha).2
    have cb : ¬hot b := (Finset.mem_filter.mp hb).2
    exact structure'.2 a b (by simpa [hot] using ca) (by simpa [hot] using cb)
  have split : W.card+F.card=S.card := by
    simpa only [W,F,Finset.card_univ,Fintype.card_coe] using
      (Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset S)) hot)
  omega
#print axioms regular_star_boundary
end ThresholdStarBypass
