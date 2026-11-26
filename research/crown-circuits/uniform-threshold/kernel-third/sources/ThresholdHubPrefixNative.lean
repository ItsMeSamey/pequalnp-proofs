import ThresholdNativeStarCap
import ThresholdHubFine
namespace ThresholdHubPrefixNative
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrExtraction ThresholdRegularSource
open ThresholdSharedPartition ThresholdSharedFlow ThresholdFlowPairs T2OrPartition
open T2CubeDeletion T2SoleOrSplice T2RegularOrDelete ThresholdHubFine
open ThresholdHubDegrees ThresholdPhysicalIdeals

theorem regular_prefix {n out : Nat} {gs : List Raw} (hn : 5≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs) (length : Nat) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    let h := (hubs C n).card
    (hotPairs L).card*length≤h*length^2+h*(budget n C.size).toNat := by
  classical
  intro C L h
  let H := hubs C n
  let Q := hotPairs L
  let idx := (H.orderIsoOfFin rfl).symm
  let rank := fun u : Id C => if hu : u∈H then (idx ⟨u,hu⟩).val else 0
  have inH (p) (hp : p∈Q) : p.1∈H ∧ p.2∈H := ((mem_pair L p.1 p.2).mp hp).1
  have injective : Set.InjOn rank (H : Set (Id C)) := by
    intro u hu v hv e
    change u∈H at hu
    change v∈H at hv
    simp only [rank,dif_pos hu,dif_pos hv] at e
    exact congrArg Subtype.val (idx.injective (Fin.ext e))
  apply ThresholdPrefixDensity.split_at Q rank h _ length
  · apply injective.mono
    intro a ha
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp ha
    exact (inH p hp).1
  · apply injective.mono
    intro b hb
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp hb
    exact (inH p hp).2
  · intro p hp
    obtain ⟨a,b⟩ := inH p hp
    have pair := (mem_pair L p.1 p.2).mp hp
    have ord : (⟨p.1,a⟩ : ↥H)<⟨p.2,b⟩ := oriented L pair.2.1 pair.2.2
    simp only [rank,dif_pos a,dif_pos b]
    exact ⟨idx.strictMono ord,(idx ⟨p.2,b⟩).isLt⟩
  · intro I hi
    have bound : ((ThresholdProbeIdeals.Cut Q I).card:ℤ)≤budget n C.size :=
      regular_ideal_cut hn minim reg (ThresholdNativeStarSaving.regular_star_cap (by omega) minim reg) I hi
    omega
#print axioms regular_prefix
end ThresholdHubPrefixNative
