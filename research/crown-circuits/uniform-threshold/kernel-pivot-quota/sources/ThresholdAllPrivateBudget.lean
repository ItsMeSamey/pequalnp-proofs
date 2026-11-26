import ThresholdNativeRowSelection
import ThresholdPrivateElimination
namespace ThresholdAllPrivateBudget
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdSecondaryReceivers ThresholdHighComponents ThresholdFanoutBudget ThresholdNativeRowSelection
open ThresholdFirstActive ThresholdLeakPins ThresholdQuarterCubes ThresholdPrivateElimination
open ThresholdPhysicalReceiverGraph
theorem native {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs) :
    let C := source gs out
    let L := layout n gs out M.eligible
    ∃ t : Nat,(allPrivate L).card≤(andIds C).length+4*t ∧ t.choose 2≤ThresholdHubMissing.M L+1 := by
  classical
  intro C L
  let R := allPrivate L
  by_cases emp : R=∅
  · exact ⟨0,by change R.card≤_; simp [emp],by simp⟩
  obtain ⟨r0,inside⟩ := Finset.nonempty_iff_ne_empty.mpr emp
  let H := high L
  have highHub : H⊆hubs C n := Finset.filter_subset _ _
  have goodR (r) (hr : r∈R) := (good_pure L (Finset.mem_filter.mp hr).1).1
  obtain ⟨inner,_,⟨outId,eo⟩⟩ := regular_inputs n gs out M.eligible reg
  let S := R.biUnion (signature C n)
  have endpin (v : ↥S) : ∃ q : Pin C, Assigned L v.val q ∧
      (∀ p,ThresholdEffectiveColumns.feeds L v.val p → p=q) ∧ ¬ReadsOR L (n+v.val.val) := by
    obtain ⟨r,hr,rv⟩ := Finset.mem_biUnion.mp v.property
    have rh := (Finset.mem_filter.mp (goodR r hr)).1
    obtain ⟨z,rz,_⟩ := shared_common L rh rh
    obtain ⟨_,_,x,rx⟩ := Finset.mem_filter.mp rz
    exact private_socket L M H x r v.val (goodR r hr) (by simp [rx]) rv
      (Finset.disjoint_left.mp (Finset.mem_filter.mp hr).2 rv)
  let site := fun v : ↥S => (endpin v).choose
  have uniq : Function.Injective site := by
    intro a b eq
    have ha := (endpin a).choose_spec.1.2
    have hb := (endpin b).choose_spec.1.2
    change port L (site a).1 (site a).2=_ at ha
    change port L (site b).1 (site b).2=_ at hb
    rw [eq,hb] at ha
    exact Subtype.ext (Fin.ext (Nat.add_left_cancel ha.symm))
  have pair (r) (hr : r∈R) : ∃ a b : ↥S,a≠b ∧ signature C n r={a.val,b.val} := by
    obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp (signature_two L inner M hn H highHub r (goodR r hr))
    exact ⟨⟨a,Finset.mem_biUnion.mpr ⟨r,hr,by change _ ∈ signature C n r; rw [eq]; simp⟩⟩,
      ⟨b,Finset.mem_biUnion.mpr ⟨r,hr,by change _ ∈ signature C n r; rw [eq]; simp⟩⟩,fun e => ab (congrArg Subtype.val e),eq⟩
  let repr (r : Id C) : ↥R := if h : r∈R then ⟨r,h⟩ else ⟨r0,inside⟩
  let left := fun r => (pair (repr r).val (repr r).property).choose
  let right := fun r => (pair (repr r).val (repr r).property).choose_spec.choose
  have info (r) (hr : r∈R) : left r≠right r ∧ signature C n r={(left r).val,(right r).val} := by
    simpa only [left,right,repr,dif_pos hr] using (pair r hr).choose_spec.choose_spec
  let same := R.filter (fun r => (site (left r)).1=(site (right r)).1)
  let D := R \ same
  have samecap : same.card≤(andIds C).length := by
    apply le_trans (ThresholdQuarterRetention.same_gate_bound R (andIds C).toFinset left right site ?_
      (fun r hr => (info r hr).1) uniq ?_) (List.toFinset_card_le _)
    · intro r _
      have op := (endpin (left r)).choose_spec.1.1
      have non : isOr C (site (left r)).1=false := by
        cases q : isOr C (site (left r)).1 with
        | false => rfl
        | true => have h := (physical_op L _).mp q; change L.op (site (left r)).1=.and at op; simp_all
      simp [andIds,non]
    · intro r hr s hs eq
      apply signatures_injective M reg H (high_common L) (goodR r hr) (goodR s hs)
      have lifted := congrArg (Finset.image (fun v : ↥S => v.val)) eq
      rw [(info r hr).2,(info s hs).2]
      simpa only [Finset.image_insert,Finset.image_singleton] using lifted
  let pins (r : Id C) : TwoPins (Id C) :=
    if h : (site (left r)).1=(site (right r)).1 then
      ⟨(site (left r)).1,(site (left r)).1,(site (left r)).2,(site (left r)).2,fun _ => rfl⟩
    else ⟨(site (left r)).1,(site (right r)).1,(site (left r)).2,(site (right r)).2,fun e => False.elim (h e)⟩
  let A := (Finset.univ : Finset (Fin n)).image (endpoints L)
  have simple := classified_simple hn M reg
  have holes := missing_global L simple.1 simple.2.1 D (fun r hr => highHub
    (Finset.mem_filter.mp (goodR r (Finset.mem_sdiff.mp hr).1)).1)
  obtain ⟨t,ts,tc⟩ := ThresholdQuarterRetention.finite_bound D pins A (ThresholdHubMissing.M L) holes (by
    intro pick
    let T := ThresholdQuarterRetention.retained D pins pick
    have tr (r) (hr : r∈T) : r∈R := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr).1).1
    apply one_pair L M inner (by rw [eo]; have := outId.isLt; omega) H T (fun r hr => goodR r (tr r hr)) pick
    · intro r hr v hv
      let col : ↥S := ⟨v,Finset.mem_biUnion.mpr ⟨r,tr r hr,hv⟩⟩
      exact (endpin col).choose_spec.2.2
    · intro r hr v hv j b _ feed
      have outside := (Finset.mem_sdiff.mp (Finset.mem_filter.mp hr).1).2
      have different : (site (left r)).1≠(site (right r)).1 := fun e => outside (Finset.mem_filter.mpr ⟨tr r hr,e⟩)
      have fit : ThresholdQuarterCubes.Fits (pins r) pick := (Finset.mem_filter.mp hr).2
      simp only [pins,dif_neg different,ThresholdQuarterCubes.Fits] at fit
      rw [(info r (tr r hr)).2] at hv
      have go (col : ↥S) (e : v=col.val) (value : pick (site col).1=(site col).2) : pick j=b := by
        have wire : ThresholdEffectiveColumns.feeds L col.val (j,b) := by
          cases b <;> simpa [ThresholdEffectiveColumns.feeds,ThresholdEffectiveColumns.wire,port,e] using feed
        have eq : (j,b)=site col := (endpin col).choose_spec.2.1 (j,b) wire
        exact (congrArg (fun p : Pin C => pick p.1) eq).trans (value.trans (congrArg Prod.snd eq).symm)
      rcases Finset.mem_insert.mp hv with e|e
      · exact go _ e fit.1
      · exact go _ (Finset.mem_singleton.mp e) fit.2)
  have partition : D.card+same.card=R.card := Finset.card_sdiff_add_card_eq_card (Finset.filter_subset _ _)
  exact ⟨t,by change R.card≤_; omega,tc⟩
end ThresholdAllPrivateBudget
