import ThresholdWarmSimple
import ThresholdColdMatchingLoss
namespace ThresholdHotMatching
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdFanoutBudget
open ThresholdEffectiveColumns ThresholdEffectiveSimplicity ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdStarBypass ThresholdOrGroups T2SoleOrSplice
open T2CubeDeletion T2RegularOrDelete ResidualSurplus ThresholdSharedFlow ThresholdPhysicalChangeEscape
open private earlier from ThresholdOrGroups
theorem native_either {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (xy : x≠y) (F A : Id (source gs out)) (fa : F≠A) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    endpoints L y={F,A} →
    ∃ r∈endpoints L y,
    Escapes L r (fun i => changedWire (C:=C) (vector {x}) (vector {x,y}) (n+i.val)) := by
  intro C L ends
  obtain ⟨_,two,q,obs⟩ := regular_inputs n gs out minim.eligible reg
  have off (z : Fin n) : (C.wires (vector {z})).getD C.output false=false := by
    cases e : (C.wires (vector {z})).getD C.output false with
    | false => rfl
    | true => have impossible := (minim.eligible.1 {z}).mp e; simp at impossible
  have out2 := (minim.eligible.1 {x,y}).mpr (by simp [xy])
  have delta : changedWire (C:=C) (vector {x}) (vector {x,y}) (n+q.val) := by
    change (C.wires (vector {x,y})).getD C.output false=true at out2
    unfold changedWire; rw [←obs,off,out2]; decide
  have only (w : Nat) (hw : w<n) (change : changedWire (C:=C) (vector {x}) (vector {x,y}) w) : w=y.val := by
    by_contra ne
    apply change
    change (ResidualSurplus.run C.gates (vector {x})).getD w false = (ResidualSurplus.run C.gates (vector {x,y})).getD w false
    rw [earlier _ _ _ (by simpa [vector] using hw),earlier _ _ _ (by simpa [vector] using hw)]
    have diff : (⟨w,hw⟩ : Fin n)≠y := fun h => ne (congrArg Fin.val h)
    rw [vec_get,vec_get]
    simp [hw,diff]
  obtain ⟨p,ps,raw,walk,changed,tail⟩ := backtrack L _ _ (by simp [vector]) (by simp [vector]) y only q delta
  have memF : F∈endpoints L y := by rw [ends]; simp
  have memA : A∈endpoints L y := by rw [ends]; simp
  obtain ⟨_,pF,rf,of'⟩ := ThresholdPivotWitness.endpoint_pin L y F memF
  obtain ⟨_,pA,ra,oa⟩ := ThresholdPivotWitness.endpoint_pin L y A memA
  have apart : pF≠pA := fun e => fa (of'.symm.trans ((congrArg (fun p : Id C × Bool => owner C n p.1) e).trans oa))
  let Z := ThresholdStarRawSlots.fiber L y
  have size : Z.card=2 := (ThresholdStarRawSlots.all_fiber L _).trans (two _ y.isLt)
  have sub : ({pF,pA} : Finset _)⊆Z := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl|hz
    · simpa [Z,ThresholdStarRawSlots.fiber] using rf
    · obtain rfl := Finset.mem_singleton.mp hz
      simpa [Z,ThresholdStarRawSlots.fiber] using ra
  have eq := Finset.eq_of_subset_of_card_le sub (by simpa [size,apart])
  have here : p∈Z := by
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _,raw⟩
  rw [←eq] at here
  have suff := owner_suffix L walk obs _ ⟨changed,tail⟩
  have member : owner C n p.1∈endpoints L y := by
    rcases Finset.mem_insert.mp here with h|h
    · rw [h]; exact of'.symm ▸ memF
    · rw [Finset.mem_singleton.mp h]; exact oa.symm ▸ memA
  refine ⟨_,member,suff.2 ?_⟩
  intro eq
  have hot := endpoint_hot L {y} y _ (by simp) member
  rw [eq,←obs,off] at hot
  contradiction

open private warm_fixed from ThresholdWarmSimple
theorem hot_blocks {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out))
    (reg : Regular n gs) (hn : 2≤n) (x y : Fin n) (xy : x≠y) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    (∀ r∈endpoints L y,∀ w∈effective L minim r,ThresholdWarmSimple.lit (C:=C) x w) → False := by
  intro C L hot
  have simple := classified_simple hn minim reg
  obtain ⟨F,A,fa,ends⟩ := Finset.card_eq_two.mp (simple.1 y)
  obtain ⟨r,hr,q,p,ps,edge,rest,mark,path⟩ := native_either minim reg x y xy F A fa ends
  exact exclude_change L minim edge rest mark path (fun v hv => warm_fixed minim x y v (hot r hr v hv))

theorem fiber_unique {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (pool missing cold : Finset (Finset (Id (source gs out))))
    (box : Finset (Id (source gs out)) → Finset (Id (source gs out)))
    (actual : ∀ p∈pool,p∉missing → p∉cold →
      ∃ x : Fin n,endpoints (layout n gs out minim.eligible) x=p ∧
        ∀ v∈box p,ThresholdWarmSimple.lit (C:=source gs out) x v)
    (covers : ∀ p∈pool,∀ r∈p,effective (layout n gs out minim.eligible) minim r⊆box p)
    (b : Finset (Id (source gs out))) :
    ((ThresholdColdMatchingLoss.fiber pool box b) \ (missing∪cold)).card≤1 := by
  classical
  apply Finset.card_le_one.mpr
  intro p hp q hq
  by_contra ne
  obtain ⟨fp,noP⟩ := Finset.mem_sdiff.mp hp
  obtain ⟨fq,noQ⟩ := Finset.mem_sdiff.mp hq
  obtain ⟨pp,pb⟩ := Finset.mem_filter.mp fp
  obtain ⟨qp,qb⟩ := Finset.mem_filter.mp fq
  obtain ⟨x,xe,xh⟩ := actual p pp (fun h => noP (Finset.mem_union_left _ h)) (fun h => noP (Finset.mem_union_right _ h))
  obtain ⟨y,ye,_⟩ := actual q qp (fun h => noQ (Finset.mem_union_left _ h)) (fun h => noQ (Finset.mem_union_right _ h))
  have xy : x≠y := by intro eq; subst y; exact ne (xe.symm.trans ye)
  apply hot_blocks minim reg hn x y xy
  intro r hr v hv
  apply xh
  rw [pb,←qb]
  exact covers q qp r (ye ▸ hr) hv
#print axioms fiber_unique
#print axioms hot_blocks
end ThresholdHotMatching
