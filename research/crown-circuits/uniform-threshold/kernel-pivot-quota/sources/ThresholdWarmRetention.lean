import ThresholdWarmSimple
namespace ThresholdWarmSimple
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdSecondaryReceivers ThresholdEffectiveColumns ThresholdColumnPeel
open scoped BigOperators
theorem two_cores {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (H R privateRows O T : Finset (Id (source gs out))) (hub : H⊆hubs (source gs out) n)
    (rows : ∀ r∈R,r∈good (source gs out) n H)
    (orig : Supported (fun v r => v∈signature (source gs out) n r) (R \ privateRows) O)
    (eff : Supported (fun v r => v∈effective (layout n gs out M.eligible) M r) (R \ privateRows) T)
    (shared : ∀ r∈R \ privateRows,∃ S∈signature (source gs out) n r,boundary (n:=n) S)
    (mu e : Nat) (space : 2*mu+e<H.card)
    (miss : ∀ r∈R \ privateRows,(missing (layout n gs out M.eligible) H r).card≤mu) :
    let L := layout n gs out M.eligible
    let B := R.filter (fun r => e+1≤(exceptional L M H r).card)
    ∃ K⊆R \ privateRows, ∃ G⊆K \ B,
      MinTwo (fun v r => v∈signature (source gs out) n r) K ∧
      MinTwo (fun v r => v∈effective L M r) G ∧
      (∀ a∈G,(effective L M a).card=2) ∧ Set.InjOn (effective L M) (G : Set _) ∧
      R.card≤G.card+privateRows.card+B.card+O.card+T.card ∧
      (e+1)*B.card≤∑ r∈R,(exceptional L M H r).card := by
  classical
  intro L B
  obtain ⟨K,ks,G,gt,origCore,finalCore,loss⟩ := two_stage
    (fun v r => v∈signature (source gs out) n r) (fun v r => v∈effective L M r)
    O T R privateRows B orig eff
  have sub : G⊆K := gt.trans Finset.sdiff_subset
  have krows (r) (hr : r∈K) := rows r (Finset.mem_sdiff.mp (ks hr)).1
  have bound (r) (hr : r∈G) : (exceptional L M H r).card≤e := by
    have no := (Finset.mem_sdiff.mp (gt hr)).2
    have inR := (Finset.mem_sdiff.mp (ks (sub hr))).1
    by_contra! large
    exact no (Finset.mem_filter.mpr ⟨inR,large⟩)
  obtain ⟨card,inj⟩ := retained_simple hn M reg H K G hub sub krows origCore
    (fun r hr => shared r (ks (sub hr))) mu e space (fun r h => miss r (ks h)) bound
  exact ⟨K,ks,G,gt,origCore,finalCore,card,inj,loss,bad_cost R (fun r => (exceptional L M H r).card) (e+1)⟩
end ThresholdWarmSimple
