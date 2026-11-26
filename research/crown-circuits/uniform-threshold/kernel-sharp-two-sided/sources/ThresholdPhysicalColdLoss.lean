import ThresholdCompetingColdCharges
import ThresholdHotMatching

namespace ThresholdPhysicalColdLoss
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSecondaryReceivers
open ThresholdColdMatchingLoss ThresholdCompetingColdCharges

/-- Physical competing cold charges and missing unordered row pairs pay the
per-box deficiency. The supplied box/candidate representation and alternate
matchings refer to the final simple graph; all quota tests use retained. -/
theorem aggregate {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (retained H : Finset (Id (source gs out)))
    (hg : ∀ r∈retained,r∈good (source gs out) n H)
    (hp : ∀ r∈retained,(makeBlock (layout n gs out M.eligible) Fin.val r).exts=[])
    (G : SimpleGraph (Id (source gs out))) [DecidableRel G.Adj]
    (edge : Id (source gs out) → Sym2 (Id (source gs out)))
    (boxes pool missing cold : Finset (Finset (Id (source gs out))))
    (box : Finset (Id (source gs out)) → Finset (Id (source gs out)))
    (A B S : Finset (Id (source gs out)) → Id (source gs out))
    (orient : ∀ p∈cold,p={A p,B p})
    (simple : Set.InjOn edge ((cold.image B : Finset _) : Set _))
    (distinct : ∀ p∈cold,B p≠S p)
    (physical : ∀ p∈cold,
      let L := layout n gs out M.eligible
      ∃ (P : Id (source gs out)) (x : Fin n), A p∈retained ∧ A p≠B p ∧
        endpoints L x={B p,A p} ∧ P≠S p ∧ signature (source gs out) n (A p)={S p,P} ∧
        2≤(readers (source gs out) (n+(S p).val)).length ∧
        ∃ v∈ThresholdEffectiveColumns.effective L M (A p),
          ((source gs out).wires (vector {x})).getD (n+v.val) false=false)
    (alternate : ∀ p∈cold,∃ T a b c d,
      let L := layout n gs out M.eligible
      let eb := ThresholdEffectiveColumns.effective L M (B p)
      (∀ v∈eb,edge (B p)∈G.incidenceFinset v) ∧ G.Adj a b ∧ G.Adj c d ∧
      ({a,b} : Finset _)∪{c,d}={S p,T}∪eb ∧
      ({a,b} : Finset _)≠{S p,T} ∧ ({c,d} : Finset _)≠{S p,T})
    (actual : ∀ p∈pool,p∉missing → p∉cold →
      ∃ x : Fin n,endpoints (layout n gs out M.eligible) x=p ∧
        ∀ v∈box p,ThresholdWarmSimple.lit (C:=source gs out) x v)
    (covers : ∀ p∈pool,∀ r∈p,
      ThresholdEffectiveColumns.effective (layout n gs out M.eligible) M r⊆box p) :
    loss boxes pool box ≤ missing.card+2*∑ v,G.degree v ^ 2 := by
  classical
  apply loss_le_missing_add_degree_squares G boxes pool missing cold box
    (fun p => edge (B p)) S (fun b _ _ => ThresholdHotMatching.fiber_unique hn M reg pool missing cold box actual covers b)
  · intro p mem
    obtain ⟨T,a,b,c,d,inc,ab,cd,cover,one,two⟩ := alternate p mem
    exact reach_of_four G _ _ _ T a b c d inc ab cd cover one two
  · apply physical_fiber hn M reg retained H hg hp edge cold A B S orient simple distinct
    intro p mem
    obtain ⟨P,x,hr,ne,raw,ps,sig,sh,off⟩ := physical p mem
    exact (orient_native _ M retained hr ne raw ps sig sh off).2

#print axioms aggregate
end ThresholdPhysicalColdLoss
