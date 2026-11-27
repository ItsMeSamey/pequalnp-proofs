import Enriched30Pivot
import ChangingDonorLive

namespace Enriched30Candidate

open PEqualNP.CircuitLowerBounds SignedTrace
open Enriched30Pivot
open ScalarFork.PhysicalLiveIncidence

/-- Agreement on all 1024 fixed-bank physical cell signatures. -/
def Realizes (C : Circuit) : Prop := ∀ c : Cell, C.eval (bits c) = label c

theorem mandatory_mem (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (h : Realizes C) (j : Nat) (hj : j ∈ mandatory) :
    j ∈ (vertices C 30).filter (fun w => w < 30) := by
  obtain ⟨a,b,hlabels,lo,hi,agree⟩ := mandatory_pivot j hj
  have flip : Physical.DonorFlip 30 j (bits a) (bits b) :=
    ⟨bits_length a, bits_length b, lo, hi, agree⟩
  apply changing_donor_mem C good flip
  rw [h a,h b]
  exact hlabels

theorem mandatory_live (C : Circuit) (good : ∀ g ∈ C.gates, Gates.Good g)
    (h : Realizes C) (j : Nat) (hj : j ∈ mandatory) : LiveUses.Live C 30 j :=
  canonical_vertices.mp (Finset.mem_filter.mp (mandatory_mem C good h j hj)).1

/-- Fixed bank slot 2 names original donor wire 89. -/
theorem realizes_binate (C : Circuit) (h : Realizes C) : Physical.BinateDonor C 30 2 := by
  obtain ⟨a,b,ha,hb,lo,hi,ab⟩ := donor89_rise
  obtain ⟨c,d,hc,hd,lc,hd',cd⟩ := donor89_fall
  exact ⟨⟨bits a,bits b,⟨bits_length a,bits_length b,lo,hi,ab⟩,
      (h a).trans ha,(h b).trans hb⟩,
    ⟨bits c,bits d,⟨bits_length c,bits_length d,lc,hd',cd⟩,
      (h c).trans hc,(h d).trans hd⟩⟩

end Enriched30Candidate
