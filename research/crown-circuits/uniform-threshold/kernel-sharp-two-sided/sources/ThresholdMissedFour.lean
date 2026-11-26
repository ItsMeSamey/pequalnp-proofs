import ThresholdEndpointPorts
import ThresholdFactorCut
import ThresholdSharedPartition

namespace ThresholdMissedFour
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups ThresholdOrExtraction
open ThresholdRegularSource ThresholdSimpleIncidence T2SoleOrSplice T2OrPartition
open ThresholdFirstActive ThresholdSharedPartition ThresholdSharedOrBudget

private theorem details {C : Circuit} {n} {L : Layout C n} {x : Fin n} {r : Id C}
    (hr : r ∈ endpoints L x) (avoids : r ∉ sharedOrs C n) {q : Id C × Bool}
    (assigned : Assigned L r q) : ∃ t : Tree, ∃ p : Nat,
      Block.group p t ∈ forest L Fin.val ∧ x.val ∈ t.raws ∧ t.out=n+r.val ∧
      readers C t.out=[q.1] := by
  have raw := (Finset.mem_filter.mp hr).2
  change x.val ∈ labels L r at raw
  unfold labels at raw
  split at raw
  next hs =>
    have stop : T2OrPartition.next C n r = none := by simpa using hs
    have ro : L.op r=.or := by
      unfold makeBlock at raw
      split at raw
      · simp [rawList] at raw
      · assumption
    have isor := (physical_op L r).mpr ro
    have short : (readers C (n+r.val)).length < 2 := by
      by_contra! big
      exact avoids (by simp [sharedOrs,sharedGates,isor,big])
    have use : q.1 ∈ readers C (n+r.val) := by
      apply read_mem
      rw [layout_inputs (L.atIndex q.1)]
      obtain ⟨j,b⟩ := q
      have hb := assigned.2
      cases b <;> simp_all [port]
    have single : readers C (n+r.val)=[q.1] := by
      cases e : readers C (n+r.val) with
      | nil => simp [e] at use
      | cons a bs =>
        cases bs with
        | nil =>
          have h : q.1=a := by simpa [e] using use
          simp [h]
        | cons b tl => simp [e] at short
    have member := mem_roots L Fin.val r stop
    have mout := makeBlock_out L Fin.val r
    cases e : makeBlock L Fin.val r with
    | meet => simp [e,rawList] at raw
    | group p t =>
      rw [e] at member raw mout
      change t.out=n+r.val at mout
      exact ⟨t,p,member,raw,mout,by rwa [mout]⟩
  next => simp at raw

theorem missed_bound {C : Circuit} {n} (L : Layout C n) (M : LexMinimum n C)
    (reg : MeetsInternal L) (hn : 2≤n) (two : ∀ x, (endpoints L x).card=2) :
    (missed L).card ≤ 4 := by
  classical
  have avoid : ∀ x ∈ missed L, ∀ r ∈ endpoints L x, r ∉ sharedOrs C n := by
    intro x hx r hr shared
    have empty := (Finset.mem_filter.mp hx).2
    change hits L x=∅ at empty
    have mem : r ∈ hits L x := Finset.mem_inter.mpr ⟨hr,by simpa [hubs] using shared⟩
    rw [empty] at mem
    simp at mem
  apply four_of_no_common_reader M reg (missed L) (fun x _ => two x) avoid
  intro x hx r hr s hs ne q v aq av
  obtain ⟨a,p,aa,xa,ao,ru⟩ := details hr (avoid x hx r hr) aq
  obtain ⟨b,t,bb,xb,bo,rv⟩ := details hs (avoid x hx s hs) av
  apply ThresholdFactorCut.private_groups_distinct_readers L Fin.val reg M hn x a b p t q.1 v.1 aq.1 aa bb xa xb _ ru rv
  intro eq
  rw [ao,bo] at eq
  exact ne (Fin.ext (Nat.add_left_cancel eq))

#print axioms missed_bound
end ThresholdMissedFour
