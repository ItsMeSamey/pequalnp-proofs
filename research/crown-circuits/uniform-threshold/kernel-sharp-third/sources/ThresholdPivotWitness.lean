import ThresholdPivotStar
import ThresholdSecondaryReceivers
namespace ThresholdPivotWitness
open PEqualNP.CircuitLowerBounds ThresholdOrExtraction ThresholdOrGroups T2OrPartition ThresholdLeakPins
open ThresholdSimpleIncidence ThresholdRegularSource ThresholdPivotStar ThresholdSecondaryReceivers
variable {C : Circuit} {n k : Nat} (L : Layout C n)

private theorem pin_of_read (i : Id C) (w : Nat) (read : w∈(C.gates.get i).inputs) :
    ∃ b : Bool,source L (i,b)=w := by
  rw [layout_inputs (L.atIndex i)] at read
  rcases List.mem_cons.mp read with h|h
  · exact ⟨false,h.symm⟩
  · exact ⟨true,(List.mem_singleton.mp h).symm⟩

private theorem raw_branch (i : Id C) (w t : Nat) (read : w∈(C.gates.get i).inputs)
    (hit : t∈(branch C n (n+i.val) w).val.raws) :
    ∃ p : Pin C,source L p=t ∧ owner C n p.1=owner C n i := by
  rw [branch] at hit
  split at hit
  · have eq : t=w := by simpa [Tree.raws] using hit
    obtain ⟨b,hb⟩ := pin_of_read L i w read
    exact ⟨(i,b),hb.trans eq.symm,rfl⟩
  · split at hit
    next ex =>
      let d := ex.choose
      have eq : w=n+d.val := ex.choose_spec.1
      obtain ⟨j,edge,idx⟩ := ex.choose_spec.2.1
      have ji : j.val=i := Fin.ext (Nat.add_left_cancel idx.symm)
      have ow : owner C n d=owner C n i := (owner_of_next C n d j edge).trans (congrArg (owner C n) ji)
      let witnesses := ex.choose_spec.2.2
      let x := witnesses.choose
      let y := witnesses.choose_spec.choose
      have gate : GateAt C n w .or x y := witnesses.choose_spec.choose_spec
      have gate' : GateAt C n (n+d.val) .or x y := eq ▸ gate
      have ins := layout_inputs gate'
      change t∈(branch C n w x).val.raws ++ (branch C n w y).val.raws at hit
      rw [←ow]
      rcases List.mem_append.mp hit with a|b
      · rw [eq] at a
        exact raw_branch d x t (by rw [ins]; simp) a
      · rw [eq] at b
        exact raw_branch d y t (by rw [ins]; simp) b
    next => simp [Tree.raws] at hit
termination_by w
decreasing_by all_goals first | exact gate.leftEarlier | exact gate.rightEarlier

theorem endpoint_pin (x : Fin n) (v : Id C) (mem : v∈endpoints L x) :
    next C n v=none ∧ ∃ p : Pin C, source L p=x.val ∧ owner C n p.1=v := by
  have lab : x.val∈labels L v := by simpa [endpoints] using mem
  cases step : next C n v with
  | some a => simp [labels,step] at lab
  | none =>
    refine ⟨rfl,?_⟩
    have hit : x.val∈rawList (makeBlock L Fin.val v) := by simpa [labels,step] using lab
    rw [←owner_of_stop C n v step]
    unfold makeBlock at hit
    split at hit
    · simp [rawList] at hit
    · change x.val∈(branch C n (n+v.val) (L.left v)).val.raws ++
          (branch C n (n+v.val) (L.right v)).val.raws at hit
      have ins := layout_inputs (L.atIndex v)
      rcases List.mem_append.mp hit with a|b
      · exact raw_branch L v _ _ (by rw [ins]; simp) a
      · exact raw_branch L v _ _ (by rw [ins]; simp) b

private theorem port_at (u v : Id C) (hv : v∈signature C n u) :
    ∃ p : Pin C, source L p=n+u.val ∧ owner C n p.1=v ∧ p.1∈readers C (n+u.val) := by
  obtain ⟨i,hi,eq⟩ := List.mem_map.mp (List.mem_toFinset.mp hv)
  obtain ⟨b,hb⟩ := pin_of_read L i _ (ThresholdFanoutBudget.reader_pin hi)
  exact ⟨(i,b),hb,eq,hi⟩

private theorem count_ports (w : Nat) :
    (Finset.univ.filter (fun p : Pin C => source L p=w)).card=(readers C w).length := by
  classical
  have count : (Finset.univ.filter (fun p : Pin C => source L p=w)).card =
      ∑ p : Pin C, if source L p=w then (1 : Nat) else 0 := by simp
  rw [count,Fintype.sum_prod_type]
  unfold readers
  rw [Fin.sum_univ_def,List.length_flatMap]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  rw [Fintype.sum_bool,layout_inputs (L.atIndex i)]
  by_cases hl : L.left i=w <;> by_cases hr : L.right i=w <;> simp [source,hl,hr]

/-- A raw edge at F and a pair of distinct receiver groups for each chosen
pure, two-reader row supply every physical witness in the star. -/
noncomputable def extract (F S : Id C) (rows : Fin k ↪ Id C) (H : Finset (Id C))
    (fs : F≠S) (rowF : ∀ x,rows x≠F)
    (edges : ∀ x,∃ a : Fin n,endpoints L a={F,rows x})
    (goodRow : ∀ x,rows x∈good C n H)
    (share : ∀ x,S∈signature C n (rows x))
    (priv : ∀ x,∃ P∈signature C n (rows x),P≠S)
    (clean : ∀ x,(makeBlock L Fin.val (rows x)).exts=[]) : Star C n k L := by
  classical
  let a := fun x => (edges x).choose
  have ends (x) : endpoints L (a x)={F,rows x} := (edges x).choose_spec
  have distinct : Function.Injective a := by
    intro x y eq
    have mem : rows x∈endpoints L (a y) := eq ▸ (by simp [ends] : rows x∈endpoints L (a x))
    exact rows.injective (by simpa [ends,rowF] using mem)
  have fpin (x) := (endpoint_pin L (a x) F (by simp [ends])).2
  have rpin (x) := endpoint_pin L (a x) (rows x) (by simp [ends])
  let sp := fun x => (port_at L (rows x) S (share x)).choose
  let spf := fun x => (port_at L (rows x) S (share x)).choose_spec
  let v := fun x => (priv x).choose
  let pp := fun x => (port_at L (rows x) (v x) (priv x).choose_spec.1).choose
  let ppf := fun x => (port_at L (rows x) (v x) (priv x).choose_spec.1).choose_spec
  refine {
    pivot := F, shared := S, rows := rows, raw := ⟨a,distinct⟩
    privatePin := pp, sharedPin := sp, distinct := fs, rowPivot := rowF
    rowShared := fun x => (receiver_later L (goodRow x) (share x)).1.ne
    ends := ends, socketFeed := fun x => (ppf x).1, sharedFeed := fun x => (spf x).1
    sharedOwner := fun x => (spf x).2.1, uses := ?_, pure := clean
    rawPivot := fun x => (fpin x).choose, rawRow := fun x => (rpin x).2.choose
    pivotFeed := fun x => (fpin x).choose_spec.1, rowFeed := fun x => (rpin x).2.choose_spec.1
    pivotGroup := fun x => (fpin x).choose_spec.2, rowGroup := fun x => (rpin x).2.choose_spec.2
    sharedOR := fun x => (physical_op L _).mp ((Finset.mem_filter.mp (goodRow x)).2.2 _ (spf x).2.2)
    rowStop := fun x => (rpin x).1 }
  intro x p hit
  have ne : pp x≠sp x := by
    intro eq
    exact (priv x).choose_spec.2 (((ppf x).2.1.symm.trans
      (congrArg (fun p : Pin C => owner C n p.1) eq)).trans (spf x).2.1)
  let Z := Finset.univ.filter (fun p : Pin C => source L p=n+(rows x).val)
  have sz : Z.card=2 := (count_ports L _).trans (Finset.mem_filter.mp (goodRow x)).2.1
  have sub : ({pp x,sp x} : Finset _)⊆Z := by
    apply Finset.insert_subset
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,(ppf x).1⟩
    · exact Finset.singleton_subset_iff.mpr (Finset.mem_filter.mpr ⟨Finset.mem_univ _,(spf x).1⟩)
  have cover := Finset.eq_of_subset_of_card_le sub (by simp [sz,ne])
  have member : p∈Z := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hit⟩
  simpa [←cover] using member
/-- Readback of the receiver deliberately chosen for the private side. -/
theorem extract_private_owner (F S : Id C) (rows : Fin k ↪ Id C) (H : Finset (Id C))
    (fs : F≠S) (rowF : ∀ x,rows x≠F)
    (edges : ∀ x,∃ a : Fin n,endpoints L a={F,rows x})
    (goodRow : ∀ x,rows x∈good C n H) (share : ∀ x,S∈signature C n (rows x))
    (priv : ∀ x,∃ P∈signature C n (rows x),P≠S)
    (clean : ∀ x,(makeBlock L Fin.val (rows x)).exts=[]) (x : Fin k) :
    let D := extract L F S rows H fs rowF edges goodRow share priv clean
    owner C n (D.privatePin x).1=(priv x).choose :=
  (port_at L (rows x) (priv x).choose (priv x).choose_spec.1).choose_spec.2.1
end ThresholdPivotWitness
