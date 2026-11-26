import ThresholdPathEndpoints
namespace ThresholdFirstActive
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2SoleOrSplice ThresholdQuarterCubes ThresholdSimpleIncidence ThresholdRegularSource
open ThresholdFanoutBudget T2OrPartition
variable {C : Circuit} {n : Nat} {L : Layout C n} {x : Fin n}

private theorem raw_lit (L : Layout C n) (t : Tree) (checked : t.Checked C n) (raw : x.val ∈ t.raws) :
    bit C {x} t.out = true := by
  have real := t.real checked (vector ({x} : Finset (Fin n))) (by simp [vector])
  have lit : bit C {x} x.val = true := (OrPath.raw (L := L) (x := x)).lit
  have a : t.raws.any (bit C {x}) = true := List.any_eq_true.mpr ⟨_,raw,lit⟩
  change bit C {x} t.out = (t.raws.any (bit C {x}) || t.exts.any (bit C {x})) at real
  simpa [a] using real

def Assigned (L : Layout C n) (r : Id C) (q : Id C × Bool) :=
    L.op q.1=.and ∧ port L q.1 q.2 = n+r.val

theorem unique_endpoint_pin (M : LexMinimum n C) (r : Id C)
    (mem : r ∈ endpoints L x) (absent : r ∉ ThresholdSharedOrBudget.sharedOrs C n) :
    ∃! q, Assigned L r q := by
  have raw := (Finset.mem_filter.mp mem).2
  change x.val ∈ labels L r at raw
  unfold labels at raw
  split at raw
  next hs =>
    have stop : T2OrPartition.next C n r = none := by simpa using hs
    have checked := makeBlock_checked L Fin.val r
    have mout := makeBlock_out L Fin.val r
    have ro : L.op r=.or := by
      unfold makeBlock at raw
      split at raw
      · simp [rawList] at raw
      · assumption
    have singleton : bit C {x} (n+r.val) = true := by
      cases eq : makeBlock L Fin.val r with
      | meet => simp [eq,rawList] at raw
      | group i t =>
        rw [eq] at checked mout raw
        exact mout ▸ raw_lit (L := L) t checked raw
    have nout : C.output ≠ n+r.val := by
      intro eq
      rw [←eq] at singleton
      have no := (M.eligible.1 {x}).mp singleton
      simp at no
    have low := live_slots L M r nout
    have isor := (physical_op L r).mpr ro
    have high : (readers C (n+r.val)).length < 2 := by
      by_contra! big
      exact absent (by simp [ThresholdSharedOrBudget.sharedOrs,ThresholdSharedOrBudget.sharedGates,isor,big])
    obtain ⟨j,one⟩ := List.length_eq_one_iff.mp (show (readers C (n+r.val)).length=1 by omega)
    have count := singleton_port one
    rw [layout_inputs (L.atIndex j)] at count
    have read : ∃! b, port L j b=n+r.val := by
      by_cases l : L.left j=n+r.val <;> by_cases r' : L.right j=n+r.val
      · simp [l,r'] at count
      · exact ⟨false,l,fun b hb => by cases b <;> simp_all [port]⟩
      · exact ⟨true,r',fun b hb => by cases b <;> simp_all [port]⟩
      · simp [l,r'] at count
    obtain ⟨b,hb,uniq⟩ := read
    have earlier : r<j := by
      cases b
      · have e := (L.atIndex j).leftEarlier; change L.left j=_ at hb; rw [hb] at e; exact Nat.lt_of_add_lt_add_left e
      · have e := (L.atIndex j).rightEarlier; change L.right j=_ at hb; rw [hb] at e; exact Nat.lt_of_add_lt_add_left e
    have andGate : L.op j=.and := by
      cases tag : L.op j with
      | and => rfl
      | or =>
        have jo := (physical_op L j).mpr tag
        simp [T2OrPartition.next,one,isor,jo,nout,earlier] at stop
    refine ⟨(j,b),⟨andGate,hb⟩,?_⟩
    rintro ⟨k,c⟩ ⟨kop,hc⟩
    have use : k ∈ readers C (n+r.val) := by
      apply read_mem
      rw [layout_inputs (L.atIndex k)]
      cases c <;> simp_all [port]
    rw [one] at use
    obtain rfl := List.mem_singleton.mp use
    exact Prod.ext rfl (uniq _ hc)
  next => simp at raw

/-- The remaining factorization input concerns a specific shared AND consumer.
    No pin assignment, path-tracing, or disjoint-subcube assumptions are required. -/
theorem four_of_no_common_reader (M : LexMinimum n C) (reg : MeetsInternal L)
    (E : Finset (Fin n)) (two : ∀ x ∈ E, (endpoints L x).card=2)
    (avoid : ∀ x ∈ E, ∀ r ∈ endpoints L x, r ∉ ThresholdSharedOrBudget.sharedOrs C n)
    (different : ∀ x ∈ E, ∀ r ∈ endpoints L x, ∀ s ∈ endpoints L x, r ≠ s →
      ∀ q q', Assigned L r q → Assigned L s q' → q.1 ≠ q'.1) : E.card ≤ 4 := by
  classical
  have desc (e : E) : ∃ p : TwoPins (Id C), CoversPorts L e.val p := by
    obtain ⟨r,s,rs,eq⟩ := Finset.card_eq_two.mp (two _ e.property)
    have hr : r ∈ endpoints L e.val := by simp [eq]
    have hs : s ∈ endpoints L e.val := by simp [eq]
    obtain ⟨q,hq,uq⟩ := unique_endpoint_pin M r hr (avoid _ e.property _ hr)
    obtain ⟨v,hv,uv⟩ := unique_endpoint_pin M s hs (avoid _ e.property _ hs)
    have diff := different _ e.property r hr s hs rs q v hq hv
    let p : TwoPins (Id C) := ⟨q.1,v.1,q.2,v.2,fun h => False.elim (diff h)⟩
    refine ⟨p,covers_of_endpoint_ports reg p (quiet_of_unshared M.eligible.1 (avoid _ e.property)) ?_⟩
    intro t ht i op b hit
    have key : Assigned L t (i,b) := ⟨op,hit⟩
    rw [eq] at ht
    rcases Finset.mem_insert.mp ht with h | h
    · subst t
      have same := uq _ key
      exact Or.inl ⟨congrArg Prod.fst same,congrArg Prod.snd same⟩
    · obtain rfl := Finset.mem_singleton.mp h
      have same := uv _ key
      exact Or.inr ⟨congrArg Prod.fst same,congrArg Prod.snd same⟩
  choose pins hp using desc
  exact avoiding_bound L M.eligible.1 M.eligible.2.1 E pins hp

end ThresholdFirstActive
