import ThresholdPhysicalChangeEscape
import ThresholdPivotQuota
import ThresholdColumnPeel
import ThresholdPrivateElimination
import ThresholdReceiverTwo
import ThresholdPublicMinimum
import ThresholdStarTruth
namespace ThresholdWarmSimple
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ResidualSurplus T2SoleOrSplice T2RegularOrDelete T2CubeDeletion
open T2OrPartition ThresholdOrExtraction ThresholdRegularSource ThresholdSimpleIncidence ThresholdSharedPartition
open ThresholdSecondaryReceivers ThresholdEffectiveColumns ThresholdEffectiveSimplicity ThresholdPhysicalChangeEscape
variable {C : Circuit} {n : Nat} (L : Layout C n)

def Edge (F A : Id C) := F≠A ∧ ∃ x : Fin n,endpoints L x={F,A}
def lit (x : Fin n) (i : Id C) := (C.wires (vector {x})).getD (n+i.val) false=true
noncomputable def missing (H : Finset (Id C)) (r : Id C) := by
  classical exact H.filter (fun F => ¬Edge L F r)
noncomputable def exceptional (M : LexMinimum n C) (H : Finset (Id C)) (r : Id C) := by
  classical exact H.filter (fun F => ∃ x : Fin n,endpoints L x={F,r} ∧ ∃ v∈effective L M r,¬lit (C:=C) x v)

/-- The pivot is excluded explicitly for every missing incident raw. The extra
exceptional set is needed only for the row already active in the baseline. -/
private theorem pivot (H A B E : Finset (Id C)) (short : A.card+B.card+E.card<H.card) :
    ∃ F∈H,F∉A ∧ F∉B ∧ F∉E := by
  classical
  by_contra! bad
  have sub : H⊆(A∪B)∪E := by
    intro f h
    by_cases a : f∈A
    · simp [a]
    by_cases b : f∈B
    · simp [b]
    · have e := bad f h a b
      simp [e]
  have cover := Finset.card_le_card sub
  have cap := Finset.card_union_le (A∪B) E
  have mid := Finset.card_union_le A B
  omega

private theorem warm_fixed {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (x y : Fin n) (v : Id (source gs out)) (hot : lit (C:=source gs out) x v) :
    ¬changedWire (C:=source gs out) (vector {x}) (vector {x,y}) (n+v.val) := by
  let C := source gs out
  have mono := ThresholdPublicMinimum.eligible_mono M.eligible
  have hop g (hg : g∈C.gates) : g.op=GateOp.and ∨ g.op=GateOp.or := by simpa using (mono g hg).1
  have bits : ThresholdStarTruth.ExtendsBits (vector {x}) (vector {x,y}) := by
    refine ⟨by simp [vector],?_⟩
    intro j; rw [vec_get,vec_get]; split <;> simp_all
  have after := (ThresholdStarTruth.gates_mono C.gates hop _ _ bits).2 (n+v.val) hot
  exact fun ne => ne (hot.trans after.symm)

private theorem different {a b F : Id C} {x y : Fin n} (ab : a≠b) (fa : F≠a)
    (xE : endpoints L x={F,a}) (yE : endpoints L y={F,b}) : x≠y := by
  intro eq
  have m : a∈endpoints L y := eq ▸ (by simp [xE] : a∈endpoints L x)
  simp [yE,Ne.symm fa,ab] at m

theorem no_parallel {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (H : Finset (Id (source gs out))) (a b : Id (source gs out)) (ab : a≠b)
    (room :
      let L := layout n gs out M.eligible
      (missing L H a).card+(missing L H b).card+(exceptional L M H a).card<H.card) :
    let L := layout n gs out M.eligible
    effective L M b≠effective L M a := by
  classical
  let L := layout n gs out M.eligible
  obtain ⟨F,inH,ma,mb,ea⟩ := pivot H _ _ _ room
  have ⟨fa,x,xe⟩ : Edge L F a := by simpa [missing,inH] using ma
  have ⟨fb,y,ye⟩ : Edge L F b := by simpa [missing,inH] using mb
  have diff := different L ab fa xe ye
  apply parallel_excluded L M (native_escape M reg x y diff F b fb (show F∈endpoints L x by rw [xe]; simp) ye)
  intro v hv
  apply warm_fixed M x y v
  by_contra cold
  exact ea (Finset.mem_filter.mpr ⟨inH,x,xe,v,hv,cold⟩)

/-- A loop's neighbor b is taken from the original core. It only needs an
incident raw for the selected pivot, even if b was later removed as cold. -/
theorem no_loop {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (H : Finset (Id (source gs out))) (K : Finset (Id (source gs out)))
    (a S : Id (source gs out)) (ha : a∈K) (sa : S∈signature (source gs out) n a)
    (rows : ∀ b∈K,b∈good (source gs out) n H)
    (origCore : ThresholdColumnPeel.MinTwo (fun v r => v∈signature (source gs out) n r) K)
    (room : ∀ b∈K,b≠a → S∈signature (source gs out) n b →
      let L := layout n gs out M.eligible
      (missing L H a).card+(missing L H b).card<H.card) :
    let L := layout n gs out M.eligible
    effective L M a≠{S} := by
  classical
  let C := source gs out
  let L := layout n gs out M.eligible
  obtain ⟨b,bk,ba,sb⟩ := origCore a ha S sa
  obtain ⟨F,inH,ma,mb,_⟩ := pivot H (missing L H a) (missing L H b) ∅
    (by simpa using room b bk ba sb)
  obtain ⟨fa,y,ye⟩ : Edge L F a := by simpa [missing,inH] using ma
  obtain ⟨fb,x,xe⟩ : Edge L F b := by simpa [missing,inH] using mb
  have diff := different L ba fb xe ye
  apply loop_excluded L M (native_escape M reg x y diff F a fa (show F∈endpoints L x by rw [xe]; simp) ye)
  apply warm_fixed M x y S
  have bHot := ThresholdStarBypass.endpoint_hot L {x} x b (by simp) (by simp [xe])
  exact ThresholdSharedPairErase.probe_le_actual L b (fun w => (C.wires (vector {x})).getD w false)
    (fun i => (L.atIndex i).eval _ (by simp [vector])) bHot _ (receiver_later L (rows b bk) sb).2

theorem retained_simple {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (M : LexMinimum n (source gs out)) (reg : Regular n gs)
    (H K G : Finset (Id (source gs out))) (hub : H⊆hubs (source gs out) n)
    (sub : G⊆K) (rows : ∀ b∈K,b∈good (source gs out) n H)
    (origCore : ThresholdColumnPeel.MinTwo (fun v r => v∈signature (source gs out) n r) K)
    (keepShared : ∀ a∈G,∃ S∈signature (source gs out) n a, boundary (n:=n) S)
    (mu e : Nat) (room : 2*mu+e<H.card)
    (missBound : ∀ a∈K,(missing (layout n gs out M.eligible) H a).card≤mu)
    (excBound : ∀ a∈G,(exceptional (layout n gs out M.eligible) M H a).card≤e) :
    let L := layout n gs out M.eligible
    (∀ a∈G,(effective L M a).card=2) ∧ Set.InjOn (effective L M) (G : Set _) := by
  classical
  let L := layout n gs out M.eligible
  have inner := (regular_inputs n gs out M.eligible reg).1
  constructor
  · intro a ha
    obtain ⟨S,sa,mark⟩ := keepShared a ha
    have present : S∈effective L M a := Finset.mem_image.mpr ⟨S,sa,column_of_boundary L M S mark⟩
    have orig := signature_two L inner M hn H hub a (rows a (sub ha))
    have cap : (effective L M a).card≤2 := (Finset.card_image_le).trans orig.le
    have no := no_loop M reg H K a S (sub ha) sa rows origCore (fun b bk _ _ => by
      have aa := missBound a (sub ha); have bb := missBound b bk; omega)
    change (effective L M a).card=2
    by_contra bad
    have small : (effective L M a).card≤1 := by omega
    apply no
    exact Finset.eq_singleton_iff_unique_mem.mpr ⟨present,fun v hv => Finset.card_le_one.mp small v hv S present⟩
  · intro a ha b hb eq
    by_contra ne
    apply no_parallel M reg H a b ne _ eq.symm
    have p := missBound a (sub ha)
    have q := missBound b (sub hb)
    have r := excBound a ha
    omega

/-- Native cold rows for fixed F,S cover all exceptions when S is a marked
original receiver of every charged row and F is an actual incident pivot. -/
theorem to_cold {n out : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (H R : Finset (Id (source gs out))) (F S a P : Id (source gs out))
    (ar : a∈R) (fa : F≠a) (mark : boundary (n:=n) S)
    (sig : signature (source gs out) n a={S,P}) (pS : P≠S)
    (bad : F∈exceptional (layout n gs out M.eligible) M H a) :
    let L := layout n gs out M.eligible
    a∈ThresholdPivotQuota.coldRows L M F S (ThresholdPivotQuota.eligible L R F S) := by
  classical
  let L := layout n gs out M.eligible
  obtain ⟨_,x,xe,v,hv,off⟩ := Finset.mem_filter.mp bad
  have eligible : a∈ThresholdPivotQuota.eligible L R F S := Finset.mem_filter.mpr
    ⟨ar,Ne.symm fa,⟨x,xe⟩,P,pS,sig⟩
  apply Finset.mem_filter.mpr
  refine ⟨eligible,x,xe,P,by simp [sig],pS,?_⟩
  obtain ⟨u,hu,rfl⟩ := Finset.mem_image.mp hv
  rw [sig] at hu
  rcases Finset.mem_insert.mp hu with eqU|mem
  · subst u; left; rw [column_of_boundary L M S mark] at off; exact Bool.eq_false_iff.mpr off
  · obtain rfl := Finset.mem_singleton.mp mem
    exact Or.inr (Bool.eq_false_iff.mpr off)
end ThresholdWarmSimple
