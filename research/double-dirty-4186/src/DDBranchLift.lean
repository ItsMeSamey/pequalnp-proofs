import DDBranchPaid
import DDRegionResources
import DDMixerRoutes
import DDLiveDAG

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Indexed Q0.Factor
attribute [local instance] gateOpDecEq

variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit} {m : ℕ}
local notation "P" => splitCuts n C (orT G C) m
local notation "V[" E "," A "," W "]" => indexed n C P E A W

private theorem inherit_influence {i w : ℕ} (h : AndPath n C i w)
    (base : Influence n C m (n+i)) : Influence n C m w := by
  induction h with
  | source => exact base
  | step _ b _ pin ih => exact .step ih b pin

private theorem indexed_direct {r j k : ℕ} (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (E : Finset ℕ) (A : Fin 2 → ℕ) (W : ℕ)
    (off : ¬ Influence n C m (n+r)) (jb : j<C.size) (ja : (gateAt C j).op=.and)
    (jp : AndPath n C j (n+r)) (b : k<C.size) (op : (gateAt C k).op=.and)
    (path : AndPath n C k (n+r)) (pin : n+j∈(gateAt C k).inputs) (notExt : j∉E) :
    (V[E,A,W]).step (.row j) (.row k) := by
  have grow := least.1.2.1 k b _ pin
  have jo : ¬ Influence n C m (n+j) := fun h => off (inherit_influence jp h)
  have ko : ¬ Influence n C m (n+k) := fun h => off (inherit_influence path h)
  obtain ⟨gj,ej⟩ := unaffected_and_paid edge least form jb ja jo
  obtain ⟨gk,ek⟩ := unaffected_and_paid edge least form b op ko
  have paid : j ∈ (V[E,A,W]).paidRows := Finset.mem_filter.mpr
    ⟨Finset.mem_range.mpr jb,by simp [ej],ja⟩
  have ne : j≠m := by rintro rfl;exact jo .source
  have rd : Node.row k ∈ (V[E,A,W]).readers j := by
    apply (indexed_reads_row C P E A W).mpr
    refine ⟨b,⟨by simp [ek],op⟩,?_⟩
    have tag := paid_ref C P ej (show j<k by omega)
    have lift (v : Fin 2) (h : opnd C k v = n+j) :
        originalSource (Indexed.pin (build n C P k) n C P k v) = some j := by
      have cut : (splitCuts n C (orT G C) m).bypass k v = false := by simp [splitCuts,h,ne]
      simp [Indexed.pin,cut,h,tag,originalSource]
    rcases Q0.reader_pin least.1 b pin with h | h
    · exact ⟨0,lift 0 h⟩
    · exact ⟨1,lift 1 h⟩
  exact ⟨paid,notExt,rd⟩

theorem region_indexed_path (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (E : Finset ℕ) (A : Fin 2 → ℕ) (W : ℕ)
    {r j : ℕ} (off : ¬ Influence n C m (n+r)) (mem : j ∈ andRegion n C r)
    (interior : ∀ i ∈ andRegion n C r, i≠r → i∉E) :
    Relation.ReflTransGen (V[E,A,W]).step (.row j) (.row r) := by
  let size := C.gates.length
  have aux (d : ℕ) : ∀ j, size-j=d → j ∈ andRegion n C r →
      Relation.ReflTransGen (V[E,A,W]).step (.row j) (.row r) := by
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro j measure mem
      obtain ⟨jb,ja,jp⟩ := in_region.mp mem
      rcases first_and_reader jp with eq | ⟨k,b,op,pin,path⟩
      · have e : j=r := by omega
        subst j
        exact .refl
      · have km := in_region.mpr ⟨b,op,path⟩
        have kr := region_wire_le least.1 km
        have grow := least.1.2.1 k b _ pin
        have bsize : k<size := b
        exact .head (indexed_direct edge least form E A W off jb ja jp b op path pin
          (interior j mem (by omega))) (ih (size-k) (by omega) k rfl km)
  exact aux _ j rfl mem

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
