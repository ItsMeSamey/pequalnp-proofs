import ThresholdPhysicalFirstCut
import ThresholdStarEndpointRows
import ThresholdStarRawSlots
import Batteries.Tactic.OpenPrivate
namespace ThresholdPivotStar
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdOrGroups ResidualSurplus T2OrPartition
open T2SoleOrSplice ThresholdSimpleIncidence ThresholdRegularSource
open ThresholdOverrideCut ThresholdPhysicalFirstCut ThresholdLeakPins
open private earlier from ThresholdOrGroups
variable {C : Circuit} {n k : Nat} (L : Layout C n)

/-- Physical sources, including both actual readers of each high row. -/
structure Star (C : Circuit) (n k : Nat) (L : Layout C n) where
  pivot : Id C
  shared : Id C
  rows : Fin k ↪ Id C
  raw : Fin k ↪ Fin n
  privatePin : Fin k → Pin C
  sharedPin : Fin k → Pin C
  distinct : pivot≠shared
  rowPivot : ∀ x,rows x≠pivot
  rowShared : ∀ x,rows x≠shared
  ends : ∀ x,endpoints L (raw x)={pivot,rows x}
  socketFeed : ∀ x,source L (privatePin x)=n+(rows x).val
  sharedFeed : ∀ x,source L (sharedPin x)=n+(rows x).val
  sharedOwner : ∀ x,owner C n (sharedPin x).1=shared
  uses : ∀ x p,source L p=n+(rows x).val → p=privatePin x ∨ p=sharedPin x
  pure : ∀ x,(makeBlock L Fin.val (rows x)).exts=[]
  rawPivot : Fin k → Pin C
  rawRow : Fin k → Pin C
  pivotFeed : ∀ x,source L (rawPivot x)=(raw x).val
  rowFeed : ∀ x,source L (rawRow x)=(raw x).val
  pivotGroup : ∀ x,owner C n (rawPivot x).1=pivot
  rowGroup : ∀ x,owner C n (rawRow x).1=rows x
  sharedOR : ∀ x,L.op (sharedPin x).1=.or
  rowStop : ∀ x,next C n (rows x)=none

variable (D : Star C n k L)
def original (s : Finset (Fin k)) (w : Nat) : Bool := (C.wires (vector (s.map D.raw))).getD w false
noncomputable def changed (s : Finset (Fin k)) (i : Id C) :=
  ThresholdOverrideCut.eval L (patch {D.pivot,D.shared} D.privatePin) s i
def hidden (i : Id C) : Prop := i≠D.pivot ∧ i≠D.shared ∧
  (owner C n i=D.pivot ∨ owner C n i=D.shared ∨ ∃ x,owner C n i=D.rows x)

theorem socket_injective : Function.Injective D.privatePin := by
  intro x y eq
  have a := D.socketFeed x
  rw [eq,D.socketFeed] at a
  exact D.rows.injective (Fin.ext (Nat.add_left_cancel a.symm))

theorem nonempty_pivot (s : Finset (Fin k)) (hs : s.Nonempty) :
    original L D s (n+D.pivot.val)=true := by
  obtain ⟨x,hx⟩ := hs
  exact ThresholdStarBypass.endpoint_hot L _ (D.raw x) D.pivot (Finset.mem_map.mpr ⟨x,hx,rfl⟩)
    (by rw [D.ends]; simp)

private theorem raw_lt (t : Tree) (c : t.Checked C n) (w : Nat) (hw : w∈t.raws) : w<n := by
  induction t with
  | raw x => obtain rfl := List.mem_singleton.mp hw; exact c
  | external => simp [Tree.raws] at hw
  | join a l r il ir => exact (List.mem_append.mp hw).elim (il c.2.1) (ir c.2.2)

theorem selected_row (s : Finset (Fin k)) (x : Fin k) :
    original L D s (n+(D.rows x).val)=decide (x∈s) := by
  have checked := makeBlock_checked L Fin.val (D.rows x)
  have out := makeBlock_out L Fin.val (D.rows x)
  have pure := D.pure x
  have label (y : Fin n) :
      y.val∈rawList (makeBlock L Fin.val (D.rows x)) ↔ D.rows x∈endpoints L y := by
    simp [endpoints,labels,D.rowStop]
  cases h : makeBlock L Fin.val (D.rows x) with
  | meet a b c => simp [h,Block.exts] at pure
  | group p t =>
    rw [h] at checked out pure label
    change t.exts=[] at pure
    change t.out=n+(D.rows x).val at out
    have eval := t.real checked (vector (s.map D.raw)) (by simp [vector])
    simp only [pure,List.any_nil,Bool.or_false] at eval
    rw [←out]
    change (C.wires _).getD t.out false=_
    rw [eval]
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true,decide_eq_true_eq]
    constructor
    · rintro ⟨j,hj,hot⟩
      have rawlt := raw_lt t checked j hj
      change (ResidualSurplus.run C.gates (vector (s.map D.raw))).getD j false=true at hot
      rw [earlier C.gates (vector (s.map D.raw)) j (by simpa [vector] using rawlt),vec_get] at hot
      simp only [dif_pos rawlt,decide_eq_true_eq] at hot
      obtain ⟨y,hy,eq⟩ := Finset.mem_map.mp hot
      have inEnds := (label (D.raw y)).mp (by simpa [eq,rawList] using hj)
      rw [D.ends] at inEnds
      have xy : x=y := D.rows.injective (by simpa [D.rowPivot] using inEnds)
      simpa [xy] using hy
    · intro hx
      have inEnds : D.rows x∈endpoints L (D.raw x) := by rw [D.ends]; simp
      have hj := (label (D.raw x)).mpr inEnds
      refine ⟨_,hj,?_⟩
      change (ResidualSurplus.run C.gates (vector (s.map D.raw))).getD (D.raw x).val false=true
      rw [earlier C.gates (vector (s.map D.raw)) (D.raw x).val (by simp [vector]),vec_get]
      simp [hx]

theorem raw_owners (twice : ∀ w : Fin n,(readers C w.val).length=2) (x : Fin k)
    (p : Pin C) (hit : source L p=(D.raw x).val) :
    owner C n p.1=D.pivot ∨ owner C n p.1=D.rows x := by
  classical
  let Z := ThresholdStarRawSlots.fiber L (D.raw x)
  have size : Z.card=2 := (ThresholdStarRawSlots.all_fiber L _).trans (twice _)
  have apart : D.rawPivot x≠D.rawRow x := by
    intro h
    exact D.rowPivot x ((D.rowGroup x).symm.trans ((congrArg (fun q : Pin C => owner C n q.1) h).symm.trans (D.pivotGroup x)))
  have sub : ({D.rawPivot x,D.rawRow x} : Finset _)⊆Z := by
    intro q h
    rcases Finset.mem_insert.mp h with rfl|h
    · simp [Z,ThresholdStarRawSlots.fiber,D.pivotFeed]
    · obtain rfl := Finset.mem_singleton.mp h
      simp [Z,ThresholdStarRawSlots.fiber,D.rowFeed]
  have eq := Finset.eq_of_subset_of_card_le sub (by simpa [size,apart])
  have mem : p∈Z := by simp [Z,ThresholdStarRawSlots.fiber,hit]
  rw [←eq] at mem
  rcases Finset.mem_insert.mp mem with rfl|h
  · exact Or.inl (D.pivotGroup x)
  · obtain rfl := Finset.mem_singleton.mp h; exact Or.inr (D.rowGroup x)

private theorem carry (v : List Bool) (len : v.length=n) (p : Pin C)
    (op : L.op p.1=.or) (on : (C.wires v).getD (source L p) false=true) :
    (C.wires v).getD (n+p.1.val) false=true := by
  rw [(L.atIndex p.1).eval v len,op]
  rcases p with ⟨i,b⟩
  cases b <;> simp_all [source,act]

include L in
private theorem owner_hot (v : List Bool) (len : v.length=n) (i : Id C)
    (on : (C.wires v).getD (n+i.val) false=true) :
    (C.wires v).getD (n+(owner C n i).val) false=true := by
  cases e : next C n i with
  | none => simpa [owner_of_stop C n i e] using on
  | some j =>
    rw [owner_of_next C n i j e]
    have mem : j.val∈readers C (n+i.val) := by simp [next_readers e]
    have pin := ThresholdFanoutBudget.reader_pin mem
    rw [layout_inputs (L.atIndex j.val)] at pin
    have hop := (ThresholdOrExtraction.physical_op L j.val).mp (next_is_or e).2
    apply owner_hot v len j.val
    rw [(L.atIndex j.val).eval v len,hop]
    rcases List.mem_cons.mp pin with a|b
    · simp only [act,←a,on,Bool.true_or]
    · have c := List.mem_singleton.mp b; simp only [act,←c,on,Bool.or_true]
termination_by C.gates.length-i.val
decreasing_by have cap := j.val.isLt; have inc := j.property; change i.val<j.val.val at inc; omega

theorem nonempty_shared (s : Finset (Fin k)) (hs : s.Nonempty) :
    original L D s (n+D.shared.val)=true := by
  obtain ⟨x,hx⟩ := hs
  rw [←D.sharedOwner x]
  apply owner_hot L _ (by simp [vector])
  apply carry L _ (by simp [vector]) (D.sharedPin x) (D.sharedOR x)
  rw [D.sharedFeed]
  simpa [original,hx] using selected_row L D s x

private theorem same_owner (p : Pin C) (j : Id C) (edge : source L p=n+j.val)
    (notStop : next C n j≠none) : owner C n j=owner C n p.1 := by
  cases z : next C n j with
  | none => contradiction
  | some a =>
    have mem := ThresholdEffectiveColumns.feeds_reader L (show ThresholdEffectiveColumns.feeds L j p from edge)
    rw [next_readers z] at mem
    rw [owner_of_next C n j a z,List.mem_singleton.mp mem]

theorem agree (twice : ∀ w : Fin n,(readers C w.val).length=2)
    (s : Finset (Fin k)) (hs : s.Nonempty) (i : Id C) (live : ¬hidden L D i) :
    changed L D s i=original L D s (n+i.val) := by
  classical
  let O := patch {D.pivot,D.shared} D.privatePin
  change ThresholdOverrideCut.eval L O s i=_
  by_cases force : i=D.pivot ∨ i=D.shared
  · have ip : i∈({D.pivot,D.shared} : Finset _) := by simpa using force
    have hot : original L D s (n+i.val)=true := by
      rcases force with rfl|rfl
      · exact nonempty_pivot L D s hs
      · exact nonempty_shared L D s hs
    rw [hot,ThresholdOverrideCut.eval]
    cases op : L.op i <;> simp [ThresholdOverrideCut.read,O,patch,ip,ThresholdOccurrenceEval.value,act]
  have notF : i≠D.pivot := fun e => force (Or.inl e)
  have notS : i≠D.shared := fun e => force (Or.inr e)
  have outside : ¬(owner C n i=D.pivot ∨ owner C n i=D.shared ∨ ∃ x,owner C n i=D.rows x) :=
    fun h => live ⟨notF,notS,h⟩
  have ip : i∉({D.pivot,D.shared} : Finset _) := by simp [notF,notS]
  have atPort (b : Bool) : ThresholdOverrideCut.read L O s (i,b) (fun j _ => ThresholdOverrideCut.eval L O s j)=
      original L D s (source L (i,b)) := by
    let p : Pin C := (i,b)
    by_cases socket : ∃ x,D.privatePin x=p
    · let x := socket.choose
      have eq : D.privatePin x=p := socket.choose_spec
      have edge := D.socketFeed x
      rw [eq] at edge
      change ThresholdOverrideCut.read L O s p _=original L D s (source L p)
      conv_rhs => rw [edge,selected_row L D s x]
      simp [ThresholdOverrideCut.read,O,patch,p,ip,socket,ThresholdOccurrenceEval.value,x]
    · have untouched : O p=none := by simp [O,patch,show p.1∉({D.pivot,D.shared} : Finset _) from ip,socket]
      change ThresholdOverrideCut.read L O s p _=original L D s (source L p)
      by_cases pred : ∃ j : Id C,source L p=n+j.val
      · simp only [ThresholdOverrideCut.read,untouched,dif_pos pred]
        let j := pred.choose
        have edge : source L p=n+j.val := pred.choose_spec
        have keep : ¬hidden L D j := by
          rintro ⟨jf,js,mask⟩
          by_cases term : next C n j=none
          · rw [owner_of_stop C n j term] at mask
            rcases mask with f|h|⟨x,eq⟩
            · exact jf f
            · exact js h
            · rw [eq] at edge
              rcases D.uses x p edge with a|a
              · exact socket ⟨x,a.symm⟩
              · exact outside (Or.inr (Or.inl (by change owner C n p.1=_; rw [a,D.sharedOwner])))
          · rw [same_owner L p j edge term] at mask
            exact outside mask
        have lt := ThresholdOccurrenceEval.earlier L p
        change source L p<n+i.val at lt
        have dec : j.val < i.val := by omega
        conv_rhs => rw [edge]
        exact agree twice s hs j keep
      · simp only [ThresholdOverrideCut.read,untouched,dif_neg pred]
        have no := pred
        have ltPort := ThresholdOccurrenceEval.earlier L p
        change source L p<n+i.val at ltPort
        have raw : source L p<n := by
          by_contra! ge
          let j : Id C := ⟨source L p-n,by have := i.isLt; omega⟩
          exact no ⟨j,by dsimp [j]; omega⟩
        have empty : (⟨source L p,raw⟩ : Fin n)∉s.map D.raw := by
          intro m
          obtain ⟨x,hx,e⟩ := Finset.mem_map.mp m
          rcases raw_owners L D twice x p (congrArg Fin.val e).symm with z|z
          · exact outside (Or.inl z)
          · exact outside (Or.inr (Or.inr ⟨x,z⟩))
        change false=(ResidualSurplus.run C.gates (vector (s.map D.raw))).getD (source L p) false
        simp only [earlier C.gates (vector (s.map D.raw)) (source L p) (by simpa [vector] using raw),vec_get,dif_pos raw,empty,decide_false]
  have rr := (L.atIndex i).eval (vector (s.map D.raw)) (by simp [vector])
  rw [ThresholdOverrideCut.eval,atPort false,atPort true]
  exact rr.symm
termination_by i.val
decreasing_by exact dec

theorem monotone (O : Override C k) (s t : Finset (Fin k)) (sub : s⊆t) (i : Id C) :
    ThresholdOverrideCut.eval L O s i=true → ThresholdOverrideCut.eval L O t i=true := by
  classical
  have side (b : Bool) : ThresholdOverrideCut.read L O s (i,b) (fun j _ => ThresholdOverrideCut.eval L O s j)=true →
      ThresholdOverrideCut.read L O t (i,b) (fun j _ => ThresholdOverrideCut.eval L O t j)=true := by
    unfold ThresholdOverrideCut.read
    cases e : O (i,b) with
    | some a =>
      cases a with
      | inl => exact id
      | inr x => simpa [ThresholdOccurrenceEval.value] using (fun h : x∈s => sub h)
    | none =>
      by_cases ex : ∃ j : Id C,source L (i,b)=n+j.val
      · simp only [dif_pos ex]
        have hit := ex.choose_spec
        have earlier := ThresholdOccurrenceEval.earlier L (i,b)
        change source L (i,b)<n+i.val at earlier
        have dec : ex.choose.val < i.val := by omega
        exact monotone O s t sub ex.choose
      · simp [ex]
  rw [ThresholdOverrideCut.eval,ThresholdOverrideCut.eval]
  have a := side false
  have b := side true
  cases L.op i <;> simp_all [act,Bool.and_eq_true,Bool.or_eq_true] <;> grind
termination_by i.val
decreasing_by exact dec

theorem output_visible (minim : LexMinimum n C) (out : Id C) (obs : C.output=n+out.val) :
    ¬hidden L D out := by
  rintro ⟨notF,notS,h⟩
  have stop : next C n out=none := by unfold next; split <;> simp [obs]
  rw [owner_of_stop C n out stop] at h
  rcases h with f|h|⟨x,eq⟩
  · exact notF f
  · exact notS h
  · have lit := selected_row L D {x} x
    have yes : C.eval (vector (({x} : Finset (Fin k)).map D.raw))=true := by
      change (C.wires _).getD C.output false=true
      rw [obs,eq]
      simpa [original] using lit
    have bad := (minim.eligible.1 _).mp yes
    simp at bad

theorem threshold (minim : LexMinimum n C) (twice : ∀ w : Fin n,(readers C w.val).length=2)
    (witness : Fin k) (out : Id C) (obs : C.output=n+out.val) (s : Finset (Fin k)) :
    changed L D s out=true ↔ 2≤s.card := by
  have nonempty (t : Finset (Fin k)) (h : t.Nonempty) :
      changed L D t out=true ↔ 2≤t.card := by
    rw [agree L D twice t h out (output_visible L D minim out obs)]
    have hh := minim.eligible.1 (t.map D.raw)
    change (C.wires _).getD C.output false=true ↔ _ at hh
    simpa [original,obs] using hh
  by_cases some : s.Nonempty
  · exact nonempty s some
  · obtain rfl := Finset.not_nonempty_iff_eq_empty.mp some
    constructor
    · intro hot
      have on := monotone L (patch {D.pivot,D.shared} D.privatePin) ∅ {witness} (Finset.empty_subset _) out hot
      have no := (nonempty {witness} (Finset.singleton_nonempty _)).mp on
      simp at no
    · simp

theorem unary (minim : LexMinimum n C) (u out : Id C) (obs : C.output=n+out.val)
    (fam : Finset (Fin k) → Prop)
    (same : ∀ s, fam s → ∀ t, fam t → ∀ x,
      ThresholdEffectiveColumns.column L minim (D.privatePin x).1≠u → (x∈s ↔ x∈t)) :
    ∃ f : Bool → Bool, ∀ s,fam s → changed L D s out=f (changed L D s u) :=
  physical_unary L minim {D.pivot,D.shared} D.privatePin u out obs fam same
theorem first_receiver (minim : LexMinimum n C) (x : Fin k) :
    ThresholdEffectiveColumns.column L minim (D.privatePin x).1=
      ThresholdEffectiveColumns.column L minim (owner C n (D.privatePin x).1) :=
  ThresholdEffectiveColumns.column_owner L minim _

theorem marked_readback (minim : LexMinimum n C) (twice : ∀ w : Fin n,(readers C w.val).length=2)
    (s : Finset (Fin k)) (hs : s.Nonempty) (u : Id C)
    (mark : ThresholdEffectiveColumns.boundary (C:=C) (n:=n) u)
    (notRow : ∀ x,u≠D.rows x) :
    changed L D s u=original L D s (n+u.val) := by
  apply agree L D twice s hs u
  rintro ⟨notF,notS,mask⟩
  have stop : next C n u=none := by
    rcases mark with obs|len
    · unfold next; split <;> simp [obs]
    · cases e : next C n u with
      | none => rfl
      | some j => rw [next_readers e] at len; simp at len
  rw [owner_of_stop C n u stop] at mask
  rcases mask with f|h|⟨x,eq⟩
  · exact notF f
  · exact notS h
  · exact notRow x eq

end ThresholdPivotStar
