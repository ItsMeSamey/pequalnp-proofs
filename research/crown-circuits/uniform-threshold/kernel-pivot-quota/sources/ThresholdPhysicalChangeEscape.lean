import ThresholdEffectiveSimplicity
import ThresholdPivotWitness
namespace ThresholdPhysicalChangeEscape
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction T2OrPartition ThresholdFanoutBudget
open ThresholdEffectiveColumns ThresholdEffectiveSimplicity ThresholdRegularSource
open ThresholdSimpleIncidence ThresholdStarBypass ThresholdOrGroups T2SoleOrSplice
variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- A walk from an interior OR to an observed output must go through the
owner, since every nonstopped vertex on the owner chain has a single reader. -/
theorem owner_suffix {i q : Id C} {ps : List (Id C×Bool)} (walk : Walk L i ps q)
    (obs : C.output=n+q.val) (chg : Id C→Prop)
    (on : chg i ∧ ∀ j∈ps.map Prod.fst,chg j) :
    chg (owner C n i) ∧ (owner C n i≠q → Escapes L (owner C n i) chg) := by
  induction walk with
  | nil i =>
    have st : next C n i=none := by
      unfold next
      split <;> simp_all
    rw [owner_of_stop C n i st]
    exact ⟨on.1,fun ne => False.elim (ne rfl)⟩
  | @cons i p ps q edge walk ih =>
    cases st : next C n i with
    | none =>
      rw [owner_of_stop C n i st]
      exact ⟨on.1,fun _ => ⟨q,p,ps,edge,walk,Or.inl obs,on.2⟩⟩
    | some j =>
      have mem := feeds_reader L edge
      rw [next_readers st] at mem
      have eq := List.mem_singleton.mp mem
      rw [owner_of_next C n i j st,←eq]
      exact ih obs ⟨on.2 _ (by simp),fun v hv => on.2 v (by simp [hv])⟩

def changedWire (a b : List Bool) (w : Nat) :=
  (C.wires a).getD w false ≠ (C.wires b).getD w false

private theorem snoc {i j : Id C} {ts : List (Id C×Bool)} (old : Walk L i ts j)
    (p : Id C×Bool) (last : feeds L j p) : Walk L i (ts++[p]) p.1 := by
  induction old with
  | nil => exact .cons last (.nil _)
  | cons ed _ ih => exact .cons ed (ih last)

theorem backtrack (a b : List Bool) (la : a.length=n) (lb : b.length=n)
    (y : Fin n) (raw : ∀ w<n,changedWire (C:=C) a b w → w=y.val)
    (q : Id C) (hq : changedWire (C:=C) a b (n+q.val)) :
    ∃ (p : Id C×Bool) (ps : List (Id C×Bool)),wire L p=y.val ∧ Walk L p.1 ps q ∧
      changedWire (C:=C) a b (n+p.1.val) ∧
      ∀ j∈ps.map Prod.fst,changedWire (C:=C) a b (n+j.val) := by
  have gate : ∃ z : Bool,changedWire (C:=C) a b (wire L (q,z)) := by
    by_contra! h
    apply hq
    unfold changedWire at *
    rw [(L.atIndex q).eval a la,(L.atIndex q).eval b lb]
    have hl := h false
    have hr := h true
    change ¬¬((C.wires a).getD (L.left q) false = (C.wires b).getD (L.left q) false) at hl
    change ¬¬((C.wires a).getD (L.right q) false = (C.wires b).getD (L.right q) false) at hr
    replace hl := not_not.mp hl
    replace hr := not_not.mp hr
    rw [hl,hr]
  obtain ⟨z,hit⟩ := gate
  let w := wire L (q,z)
  by_cases small : w<n
  · exact ⟨(q,z),[],raw w small hit,.nil _,hq,by simp⟩
  · have lt : w<n+q.val := by
      cases z <;> first | exact (L.atIndex q).leftEarlier | exact (L.atIndex q).rightEarlier
    let j : Id C := ⟨w-n,by have size := q.isLt; omega⟩
    have eq : w=n+j.val := by dsimp [j]; omega
    obtain ⟨p,ps,input,walk,first,tail⟩ := backtrack a b la lb y raw j (eq ▸ hit)
    refine ⟨p,ps++[(q,z)],input,snoc L walk (q,z) eq,first,?_⟩
    intro v hv
    rw [List.map_append] at hv
    rcases List.mem_append.mp hv with vp|vq
    · exact tail v vp
    · have ve : v=q := by simpa using vq
      simpa [ve] using hq
termination_by q.val
decreasing_by omega

open T2CubeDeletion T2RegularOrDelete ResidualSurplus ThresholdSharedFlow
open private earlier from ThresholdOrGroups
theorem native_escape {n out : Nat} {gs : List Raw} (minim : LexMinimum n (source gs out))
    (reg : Regular n gs) (x y : Fin n) (xy : x≠y) (F A : Id (source gs out)) (fa : F≠A) :
    let C := source gs out
    let L := layout n gs out minim.eligible
    F∈endpoints L x → endpoints L y={F,A} →
    Escapes L A (fun i => changedWire (C:=C) (vector {x}) (vector {x,y}) (n+i.val)) := by
  intro C L fx ends
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
  rcases Finset.mem_insert.mp here with e|e
  · rw [e,of'] at suff
    have first := suff.1
    unfold changedWire at first
    rw [endpoint_hot L {x} x F (by simp) fx,endpoint_hot L {x,y} y F (by simp) memF] at first
    contradiction
  · rw [Finset.mem_singleton.mp e,oa] at suff
    apply suff.2
    intro eq
    have hot := endpoint_hot L {y} y A (by simp) memA
    rw [eq,←obs,off] at hot
    contradiction
#print axioms native_escape
end ThresholdPhysicalChangeEscape
