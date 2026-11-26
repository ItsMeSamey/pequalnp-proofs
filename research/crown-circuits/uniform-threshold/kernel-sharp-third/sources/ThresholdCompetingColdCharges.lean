import ThresholdPivotQuota
import ThresholdColdMatchingLoss

namespace ThresholdCompetingColdCharges
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSecondaryReceivers
open ThresholdPivotQuota ThresholdColdMatchingLoss

/-- In a competing matching, choose its edge touching the original shared
endpoint S of the cold row. Its other endpoint v has to belong to B. -/
theorem cross_reach {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Sym2 V) (endsB : Finset V) (S T : V)
    (incident : ∀ v ∈ endsB, B ∈ G.incidenceFinset v)
    (alt : ∃ v, G.Adj S v ∧ v ∈ ({S,T} : Finset V) ∪ endsB ∧
      ({S,v} : Finset V) ≠ {S,T}) :
    ∃ v, B ∈ G.incidenceFinset v ∧ G.Adj v S := by
  obtain ⟨v,adj,cover,diff⟩ := alt
  refine ⟨v,incident v ?_,adj.symm⟩
  rcases Finset.mem_union.mp cover with h|h
  · simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with h|h
    · subst v
      exact False.elim (adj.ne rfl)
    · subst v
      exact False.elim (diff rfl)
  · exact h

/-- The two alternate rows cover the same four vertices. Neither equals
the original row {S,T}: in two distinct perfect matchings on a four-set
a common edge would force the complementary edge as well. -/
theorem reach_of_four {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (B : Sym2 V) (endsB : Finset V) (S T a b c d : V)
    (incident : ∀ v ∈ endsB, B ∈ G.incidenceFinset v)
    (ab : G.Adj a b) (cd : G.Adj c d)
    (cover : ({a,b} : Finset V) ∪ {c,d} = {S,T} ∪ endsB)
    (one : ({a,b} : Finset V) ≠ {S,T}) (two : ({c,d} : Finset V) ≠ {S,T}) :
    ∃ v, B ∈ G.incidenceFinset v ∧ G.Adj v S := by
  apply cross_reach G B endsB S T incident
  have hit : S ∈ ({a,b} : Finset V) ∪ {c,d} := by rw [cover]; simp
  simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hit
  rcases hit with (h|h)|(h|h)
  · subst S
    exact ⟨b,ab,by rw [←cover]; simp,one⟩
  · subst S
    exact ⟨a,ab.symm,by rw [←cover]; simp,by rw [Finset.pair_comm b a]; exact one⟩
  · subst S
    exact ⟨d,cd,by rw [←cover]; simp,two⟩
  · subst S
    exact ⟨c,cd.symm,by rw [←cover]; simp,by rw [Finset.pair_comm d c]; exact two⟩

/-- Original shared S survives as an effective endpoint, and a failed
effective-column singleton test on a two-receiver row is exactly enough
to put the oriented row in the original pivot quota domain. -/
theorem orient_native {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    (retained : Finset (Id C)) {A B S P : Id C} {x : Fin n}
    (mem : A∈retained) (ab : A≠B) (raw : endpoints L x={B,A}) (ps : P≠S)
    (sig : signature C n A={S,P}) (shared : 2≤(readers C (n+S.val)).length)
    (off : ∃ v∈ThresholdEffectiveColumns.effective L M A,
      (C.wires (vector {x})).getD (n+v.val) false=false) :
    S∈ThresholdEffectiveColumns.effective L M A ∧
      A∈eligible L retained B S ∧ Cold L M B S A := by
  classical
  have keep := ThresholdEffectiveColumns.keep_shared L M S shared
  have spec : ThresholdEffectiveColumns.effective L M A =
      {S,ThresholdEffectiveColumns.column L M P} := by
    simp [ThresholdEffectiveColumns.effective,sig,keep]
  obtain ⟨v,hv,zero⟩ := off
  rw [spec] at hv
  simp only [Finset.mem_insert,Finset.mem_singleton] at hv
  refine ⟨by rw [spec]; simp, Finset.mem_filter.mpr ⟨mem,ab,⟨x,raw⟩,P,ps,sig⟩,
    x,raw,P,by simp [sig],ps,?_⟩
  rcases hv with h|h
  · exact Or.inl (h ▸ zero)
  · exact Or.inr (h ▸ zero)

/-- A candidate is its actual unordered pair of original physical row IDs.
The orientation may vary with the candidate. Simplicity is needed only
on opposite rows that actually occur in this cold family. -/
theorem physical_fiber {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (retained H : Finset (Id (source gs out)))
    (hg : ∀ r∈retained,r∈good (source gs out) n H)
    (hp : ∀ r∈retained,(makeBlock (layout n gs out M.eligible) Fin.val r).exts=[])
    {V : Type*} [DecidableEq V]
    (edge : Id (source gs out) → Sym2 V)
    (cold : Finset (Finset (Id (source gs out))))
    (A B S : Finset (Id (source gs out)) → Id (source gs out))
    (orient : ∀ p∈cold, p={A p,B p})
    (simple : Set.InjOn edge ((cold.image B : Finset _) : Set _))
    (distinct : ∀ p∈cold, B p ≠ S p)
    (physical : ∀ p∈cold,
      let L := layout n gs out M.eligible
      A p ∈ eligible L retained (B p) (S p) ∧ Cold L M (B p) (S p) (A p))
    (e : Sym2 V) (s : Id (source gs out)) :
    (cold.filter (fun p => (edge (B p), S p)=(e,s))).card ≤ 2 := by
  classical
  let K := cold.filter (fun p => (edge (B p), S p)=(e,s))
  change K.card ≤ 2
  by_cases h : K.Nonempty
  · obtain ⟨p0,h0⟩ := h
    have props {p} (mem : p∈K) : p∈cold ∧ edge (B p)=e ∧ S p=s := by
      obtain ⟨hc,hk⟩ := Finset.mem_filter.mp mem
      exact ⟨hc, congrArg Prod.fst hk, congrArg Prod.snd hk⟩
    have eqB {p} (mem : p∈K) : B p=B p0 :=
      simple (Finset.mem_image_of_mem B (props mem).1)
        (Finset.mem_image_of_mem B (props h0).1) ((props mem).2.1.trans (props h0).2.1.symm)
    let L := layout n gs out M.eligible
    let R := eligible L retained (B p0) s
    have into : K.image A ⊆ coldRows L M (B p0) s R := by
      intro r hr
      obtain ⟨p,mem,rfl⟩ := Finset.mem_image.mp hr
      exact Finset.mem_filter.mpr (by simpa only [eqB mem,(props mem).2.2] using physical p (props mem).1)
    have inj : Set.InjOn A (K : Set _) := by
      intro p mp q mq eq
      rw [orient p (props mp).1,orient q (props mq).1,eq,eqB mp,eqB mq]
    have quota := (native hn M reg retained H (B p0) s
      (by simpa only [(props h0).2.2] using distinct p0 (props h0).1) hg hp).1
    have cnt := Finset.card_le_card into
    rw [Finset.card_image_of_injOn inj] at cnt
    exact cnt.trans quota
  · simp [Finset.not_nonempty_iff_eq_empty.mp h]

end ThresholdCompetingColdCharges
