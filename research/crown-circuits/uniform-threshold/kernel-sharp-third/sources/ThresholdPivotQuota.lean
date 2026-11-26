import ThresholdPivotWitness
import ThresholdPairContexts
namespace ThresholdPivotQuota
open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSecondaryReceivers
open ThresholdEffectiveColumns ThresholdPivotStar ThresholdPivotWitness

variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- Every retained row with the prescribed incident raw and the prescribed
two distinct original receivers belongs to the pivot experiment. -/
noncomputable def eligible (retained : Finset (Id C)) (F S : Id C) : Finset (Id C) := by
  classical
  exact retained.filter (fun r => r≠F ∧ (∃ x : Fin n,endpoints L x={F,r}) ∧
    ∃ P, P≠S ∧ signature C n r={S,P})

/-- Coldness is evaluated on a singleton of the original raw coordinates. -/
def Cold (M : LexMinimum n C) (F S r : Id C) : Prop :=
  ∃ a : Fin n, endpoints L a={F,r} ∧ ∃ P∈signature C n r,P≠S ∧
    ((C.wires (vector {a})).getD (n+S.val) false=false ∨
     (C.wires (vector {a})).getD (n+(column L M P).val) false=false)

noncomputable def coldRows (M : LexMinimum n C) (F S : Id C) (R : Finset (Id C)) := by
  classical exact R.filter (Cold L M F S)

theorem quota (M : LexMinimum n C) (twice : ∀ w : Fin n,(readers C w.val).length=2)
    (einj : Function.Injective (endpoints L)) (out : Id C) (obs : C.output=n+out.val)
    (retained H : Finset (Id C)) (F S : Id C) (fs : F≠S)
    (hg : ∀ r∈retained,r∈good C n H)
    (hp : ∀ r∈retained,(makeBlock L Fin.val r).exts=[]) :
    let R := eligible L retained F S
    (coldRows L M F S R).card≤
      if 3≤R.card then 1 else 2 := by
  classical
  intro R
  let e : Fin R.card ≃ ↥R := (R.orderIsoOfFin rfl).toEquiv
  let rows : Fin R.card ↪ Id C := e.toEmbedding.trans (Function.Embedding.subtype _)
  have mem (i) : rows i∈R := (e i).property
  have spec (i) := (Finset.mem_filter.mp (mem i)).2
  have ret (i) : rows i∈retained := (Finset.mem_filter.mp (mem i)).1
  let rf := fun i => (spec i).1
  let edge := fun i => (spec i).2.1
  let g := fun i => hg _ (ret i)
  let pure := fun i => hp _ (ret i)
  have share (i) : S∈signature C n (rows i) := by
    obtain ⟨P,ne,eq⟩ := (spec i).2.2; simp [eq]
  have priv (i) : ∃ P∈signature C n (rows i),P≠S := by
    obtain ⟨P,ne,eq⟩ := (spec i).2.2
    exact ⟨P,by simp [eq],ne⟩
  let D := extract L F S rows H fs rf edge g share priv pure
  have hotBound := cold_quota L D M out obs twice (fun hk =>
    injection L D M (physical_pair_contexts L D M) hk twice out obs)
  have transfer (i) (hc : Cold L M F S (rows i)) : i∈cold L D M := by
    obtain ⟨a,eq,P,pSig,pNe,off⟩ := hc
    have rawEq : D.raw i=a := einj ((D.ends i).trans eq.symm)
    have privateEq : (priv i).choose=P := by
      obtain ⟨Q,ne,sig⟩ := (spec i).2.2
      have p : P=Q := by simpa [sig,pNe] using pSig
      have q : (priv i).choose=Q := by
        have transMem := congrArg (fun Z : Finset (Id C) => (priv i).choose∈Z) sig
        have mem := transMem.mp (priv i).choose_spec.1
        exact Finset.mem_singleton.mp ((Finset.mem_insert.mp mem).resolve_left (priv i).choose_spec.2)
      exact q.trans p.symm
    have col : first L D M i=column L M P := by
      change column L M (D.privatePin i).1=column L M P
      rw [first_receiver L D M i]
      rw [extract_private_owner L F S rows H fs rf edge g share priv pure i,privateEq]
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_univ _,?_⟩
    rcases off with sOff|pOff
    · have sOn := nonempty_shared L D {i} (Finset.singleton_nonempty _)
      change original L D {i} (n+S.val)=true at sOn
      have bad : (C.wires (vector {a})).getD (n+S.val) false=true := by
        simpa [original,rawEq] using sOn
      exact False.elim (Bool.false_ne_true (sOff.symm.trans bad))
    · simpa [original,rawEq,col] using pOff
  have incl : (coldRows L M F S R) ⊆ (cold L D M).map rows := by
    intro r hr
    obtain ⟨inR,hc⟩ := Finset.mem_filter.mp hr
    let i := e.symm ⟨r,inR⟩
    have eq : rows i=r := congrArg Subtype.val (e.apply_symm_apply ⟨r,inR⟩)
    exact Finset.mem_map.mpr ⟨i,transfer i (eq.symm ▸ hc),eq⟩
  have cnt := Finset.card_le_card incl
  rw [Finset.card_map] at cnt
  exact cnt.trans hotBound

/-- Native fixed-key bound on the complete retained row set. -/
theorem native {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (retained H : Finset (Id (source gs out))) (F S : Id (source gs out)) (fs : F≠S)
    (hg : ∀ r∈retained,r∈good (source gs out) n H)
    (hp : ∀ r∈retained,(makeBlock (layout n gs out minim.eligible) Fin.val r).exts=[]) :
    let L := layout n gs out minim.eligible
    let R := eligible L retained F S
    let B := coldRows L minim F S R
    B.card≤2 ∧ (3≤R.card → B.card≤1) := by
  intro L R B
  obtain ⟨_,twice,j,obs⟩ := regular_inputs n gs out minim.eligible reg
  have inj := (classified_simple hn minim reg).2.1
  have q := quota L minim (fun w => twice w.val w.isLt) inj j obs retained H F S fs hg hp
  change B.card ≤ (if 3≤R.card then 1 else 2) at q
  by_cases h : 3≤R.card <;> simp [h] at q ⊢ <;> omega

#print axioms native
end ThresholdPivotQuota
