import ThresholdCompetingAlternates
namespace ThresholdActualFineLoss
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSecondaryReceivers
open ThresholdActualColdCandidates ThresholdEffectiveColumns

theorem native {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (R retained H : Finset (Id (source gs out))) (rr : R⊆retained) (rh : R⊆H)
    (hg : ∀ r∈retained,r∈good (source gs out) n H)
    (hp : ∀ r∈retained,(makeBlock (layout n gs out M.eligible) Fin.val r).exts=[])
    (G : SimpleGraph (Id (source gs out))) [DecidableRel G.Adj]
    (edge : Id (source gs out) → Sym2 (Id (source gs out)))
    (shared : Id (source gs out) → Id (source gs out))
    (outside : ∀ a∈R,shared a∉H)
    (tag : ∀ a∈R, ∃ P, P≠shared a ∧ signature (source gs out) n a={shared a,P} ∧
      2≤(readers (source gs out) (n+(shared a).val)).length)
    (fallback : Id (source gs out))
    (boxes : Finset (Finset (Id (source gs out)))) (four : ∀ F∈boxes,F.card=4) :
    let L := layout n gs out M.eligible
    let col := effective L M
    Set.InjOn col (R:Set _) → (∀ r∈R,(col r).card=2) → Set.InjOn edge (R:Set _) →
    (∀ r∈R,∀ v∈col r,edge r∈G.incidenceFinset v) →
    (∀ r∈R,∀ a b,col r={a,b} → G.Adj a b) →
    ∑ F∈boxes, ((ThresholdEffectiveMatchingRows.fiber R col F).card-1) ≤
      (missing L H).card+2*∑ v,G.degree v ^ 2 := by
  classical
  intro L col inject two edgeinj incident adj
  let A := fun p => first L M R p fallback
  let B := fun p => second L M R p fallback
  let S := fun p => shared (A p)
  have spec {p} (mem : p∈cold L M R) := oriented L M fallback mem
  have sm : Set.InjOn edge (((cold L M R).image B : Finset _) : Set _) := by
    apply edgeinj.mono
    intro r hr
    obtain ⟨p,mem,rfl⟩ := Finset.mem_image.mp hr
    exact (spec mem).2.2.2.2
  have out' {p} (mem : p∈cold L M R) : B p≠S p := by
    intro eq
    apply outside _ (spec mem).2.2.2.1
    change S p ∈ H
    rw [←eq]
    exact rh (spec mem).2.2.2.2
  have getTag {p} (mem : p∈cold L M R) := tag _ (spec mem).2.2.2.1
  have bound := ThresholdPhysicalColdLoss.aggregate hn M reg retained H hg hp G edge boxes
    (competing L M R) (missing L R) (cold L M R) (box L M) A B S
    (fun _ mem => (spec mem).1) sm (fun _ mem => out' mem)
    (by
      intro p mem
      obtain ⟨P,ps,sig,sh⟩ := getTag mem
      obtain ⟨_,x,raw,v,hv,off⟩ := (spec mem).2.2.1
      exact ⟨P,x,rr (spec mem).2.2.2.1,(spec mem).2.1,
        raw.trans ((spec mem).1.trans (Finset.pair_comm _ _)),ps,sig,sh,v,hv,off⟩)
    (by
      intro p mem
      obtain ⟨P,ps,sig,sh⟩ := getTag mem
      have touch : S p∈col (A p) := by
        change shared (A p)∈(signature _ _ (A p)).image (column L M)
        apply Finset.mem_image.mpr
        exact ⟨_,by rw [sig]; exact Finset.mem_insert_self _ _,keep_shared L M _ sh⟩
      obtain ⟨T,i,j,k,l,ij,kl,c,o,t⟩ := ThresholdCompetingAlternates.native L M G
        inject two adj mem (spec mem).1 (spec mem).2.2.2.1 (spec mem).2.2.2.2 touch
      exact ⟨T,i,j,k,l,incident _ (spec mem).2.2.2.2,ij,kl,c,o,t⟩)
    (fun _ mem => actual_hot L M mem)
    (fun p _ r hr v hv => Finset.mem_biUnion.mpr ⟨r,hr,hv⟩)
  have sumEq : (∑ F∈boxes, ((ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F).card-1)) =
      ∑ F∈boxes, ((ThresholdEffectiveMatchingRows.fiber R (effective L M) F).card-1) :=
    Finset.sum_congr rfl (fun F mem => box_deficiency L M (four F mem))
  change (∑ F∈boxes, ((ThresholdColdMatchingLoss.fiber (competing L M R) (box L M) F).card-1)) ≤ _ at bound
  rw [sumEq] at bound
  exact bound.trans (Nat.add_le_add_right (Finset.card_le_card (missing_mono L rh)) _)

#print axioms native
end ThresholdActualFineLoss
