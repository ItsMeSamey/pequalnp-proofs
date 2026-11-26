import ThresholdEdgeRealization
import Mathlib.Combinatorics.SimpleGraph.Finite
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ThresholdRegularSource
open ThresholdSimpleIncidence
namespace ThresholdGraphCounts
abbrev Vtx {C : Circuit} {n} (L : Layout C n) := {v : T2OrPartition.Id C // v∈vertices L}

def profile {C : Circuit} {n} (L : Layout C n) (p : Sym2 (Vtx L)) :=
  p.toFinset.map (pinEmbedding L)

theorem profile_injective {C : Circuit} {n} (L : Layout C n) : Function.Injective (profile L) := by
  intro a b eq
  apply Sym2.ext
  intro v
  have same := congrArg (fun p : Finset (T2OrPartition.Id C) => pinEmbedding L v ∈ p) eq
  simpa [profile] using same.to_iff

theorem realizes_raw {C : Circuit} {n} (L : Layout C n) (w : Fin n) (card : (endpoints L w).card=2) :
    ∃ p : (graph L).edgeSet, profile L p.val=endpoints L w := by
  obtain ⟨a,b,ne,h⟩ := Finset.card_eq_two.mp card
  have ha : a∈endpoints L w := by simp [h]
  have hb : b∈endpoints L w := by simp [h]
  let A : Vtx L := ⟨a,active_endpoint L w ha⟩
  let B : Vtx L := ⟨b,active_endpoint L w hb⟩
  have adj : (graph L).Adj A B := ⟨fun eq => ne (congrArg Subtype.val eq),w,ha,hb⟩
  refine ⟨⟨Sym2.mk A B,adj⟩,?_⟩
  simp [profile,Sym2.toFinset_mk_eq,h,A,B,pinEmbedding]

theorem edge_has_raw {C : Circuit} {n} (L : Layout C n) (two : ∀ w,(endpoints L w).card=2)
    (p : (graph L).edgeSet) : ∃ w,endpoints L w=profile L p.val := by
  obtain ⟨p,hp⟩ := p
  induction p using Sym2.ind with
  | _ a b =>
    obtain ⟨w,hw⟩ := edge_realized L two (show (graph L).Adj a b from hp)
    exact ⟨w,by simpa [profile,Sym2.toFinset_mk_eq] using hw⟩

noncomputable def rawEdgeEquiv {C : Circuit} {n} (L : Layout C n)
    (two : ∀ w,(endpoints L w).card=2) (inj : Function.Injective (endpoints L)) :
    Fin n ≃ (graph L).edgeSet :=
  let pick := fun w => (realizes_raw L w (two w)).choose
  Equiv.ofBijective pick ⟨fun x y eq => inj (by
    rw [←(realizes_raw L x (two x)).choose_spec,←(realizes_raw L y (two y)).choose_spec]
    exact congrArg (fun e : (graph L).edgeSet => profile L e.val) eq),fun e => by
    obtain ⟨w,hw⟩ := edge_has_raw L two e
    exact ⟨w,Subtype.ext (profile_injective L ((realizes_raw L w (two w)).choose_spec.trans hw))⟩⟩

theorem raw_profile {C : Circuit} {n} (L : Layout C n) (two : ∀ w,(endpoints L w).card=2)
    (inj : Function.Injective (endpoints L)) (w : Fin n) :
    profile L ((rawEdgeEquiv L two inj w).val)=endpoints L w :=
  (realizes_raw L w (two w)).choose_spec

theorem graph_edge_card {C : Circuit} {n} (L : Layout C n) (two : ∀ w,(endpoints L w).card=2)
    (inj : Function.Injective (endpoints L)) [Fintype (graph L).edgeSet] :
    (graph L).edgeFinset.card=n := by
  classical
  rw [SimpleGraph.edgeFinset_card]
  exact (Fintype.card_congr (rawEdgeEquiv L two inj)).symm.trans (Fintype.card_fin _)

noncomputable def rawAt {C : Circuit} {n} (L : Layout C n) (v : Vtx L) :=
  Finset.univ.filter (fun w : Fin n => v.val∈endpoints L w)

theorem degree_eq_raw {C : Circuit} {n} (L : Layout C n) (v : Vtx L)
    (two : ∀ w,(endpoints L w).card=2) (inj : Function.Injective (endpoints L))
    [Fintype ((graph L).neighborSet v)] :
    (graph L).degree v=(rawAt L v).card := by
  classical
  let E := rawEdgeEquiv L two inj
  have trace (w : Fin n) : v∈(E w).val ↔ v.val∈endpoints L w := by
    rw [←raw_profile L two inj w]
    change v∈(E w).val ↔ pinEmbedding L v∈profile L (E w).val
    simp [profile]
  let convert : (rawAt L v) → (graph L).incidenceSet v := fun w =>
    ⟨(E w.val).val,(E w.val).property,(trace _).mpr (by simpa [rawAt] using w.property)⟩
  have bij : Function.Bijective convert := by
    constructor
    · intro a b eq
      have rawEq := congrArg (fun q : (graph L).incidenceSet v => q.val) eq
      change (E a.val).val = (E b.val).val at rawEq
      exact Subtype.ext (E.injective (Subtype.ext rawEq))
    · intro e
      let b : (graph L).edgeSet := ⟨e.val,e.property.1⟩
      let w := E.symm b
      have back : E w=b := E.apply_symm_apply _
      have hit : v∈(E w).val := by rw [back]; exact e.property.2
      refine ⟨⟨w,by simpa [rawAt] using (trace w).mp hit⟩,?_⟩
      apply Subtype.ext
      change (E w).val = b.val
      exact congrArg (fun q : (graph L).edgeSet => q.val) back
  rw [←SimpleGraph.card_incidenceSet_eq_degree]
  exact (Fintype.card_congr (Equiv.ofBijective convert bij)).symm.trans (Fintype.card_coe _)

private theorem bounded_raws {C : Circuit} {n} (t : Tree) (checked : t.Checked C n) :
    ∀ j∈t.raws,j<n := by
  induction t with
  | raw i => simpa [Tree.Checked,Tree.raws] using checked
  | external i => simp [Tree.raws]
  | join i l r hl hr =>
    intro j hj
    exact (List.mem_append.mp hj).elim (hl checked.2.1 j) (hr checked.2.2 j)

theorem rawAt_nonempty {C : Circuit} {n} (L : Layout C n) (v : Vtx L) :
    (rawAt L v).Nonempty := by
  have live : labels L v.val≠[] := by simpa [vertices] using v.property
  obtain ⟨j,hit⟩ := List.exists_mem_of_ne_nil _ live
  have small : j<n := by
    have shape := makeBlock_checked L Fin.val v.val
    unfold labels at hit
    split at hit
    · cases b : makeBlock L Fin.val v.val with
      | meet j l r => simp [b,rawList] at hit
      | group p t =>
        rw [b] at shape hit
        exact bounded_raws t shape j hit
    · simp at hit
  exact ⟨⟨j,small⟩,by simpa [rawAt,endpoints] using hit⟩

theorem degree_pos {C : Circuit} {n} (L : Layout C n) (v : Vtx L)
    (two : ∀ w,(endpoints L w).card=2) (inj : Function.Injective (endpoints L))
    [Fintype ((graph L).neighborSet v)] : 0 < (graph L).degree v := by
  rw [degree_eq_raw L v two inj]
  exact Finset.card_pos.mpr (rawAt_nonempty L v)

#print axioms graph_edge_card
#print axioms degree_eq_raw
#print axioms degree_pos
end ThresholdGraphCounts
