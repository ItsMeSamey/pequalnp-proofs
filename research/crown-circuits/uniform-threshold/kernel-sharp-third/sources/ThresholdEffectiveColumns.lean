import ThresholdReceiverCounts
namespace ThresholdEffectiveColumns
open PEqualNP.CircuitLowerBounds T2OrPartition ThresholdOrExtraction ThresholdFanoutBudget T2SoleOrSplice
variable {C : Circuit} {n : Nat} (L : Layout C n)

/-- false selects the left operand and true the right operand. -/
def wire (port : Id C × Bool) := if port.2 then L.right port.1 else L.left port.1
def feeds (i : Id C) (p : Id C × Bool) := wire L p=n+i.val
def boundary (i : Id C) : Prop := C.output=n+i.val ∨ 2≤(readers C (n+i.val)).length

theorem feeds_reader {i : Id C} {p : Id C × Bool} (h : feeds L i p) :
    p.1∈readers C (n+i.val) := by
  apply read_mem
  rw [layout_inputs (L.atIndex p.1)]
  rcases p with ⟨j,b⟩
  cases b <;> simp_all [feeds,wire]

theorem feeds_later {i : Id C} {p : Id C × Bool} (h : feeds L i p) : i<p.1 := by
  rcases p with ⟨j,b⟩
  have left := (L.atIndex j).leftEarlier
  have right := (L.atIndex j).rightEarlier
  change i.val < j.val
  cases b <;> simp [feeds,wire] at h <;> omega

/-- A singleton reader list counts pins, so the chosen side is unique even
when the representation permits both operands to name the same wire. -/
theorem sole_pin {i j : Id C} (only : readers C (n+i.val)=[j]) :
    ∃ p : Id C × Bool, p.1=j ∧ feeds L i p ∧ ∀ r,feeds L i r → r=p := by
  have count := singleton_port only
  rw [layout_inputs (L.atIndex j)] at count
  have choices : (L.left j=n+i.val ∧ L.right j≠n+i.val) ∨
      (L.right j=n+i.val ∧ L.left j≠n+i.val) := by
    by_cases l : L.left j=n+i.val <;> by_cases r : L.right j=n+i.val <;>
      simp_all [List.filter_cons]
  rcases choices with ⟨left,right⟩|⟨right,left⟩
  · refine ⟨(j,false),rfl,left,?_⟩
    rintro ⟨k,b⟩ h
    have k := feeds_reader L h
    rw [only] at k
    obtain rfl := List.mem_singleton.mp k
    cases b <;> simp_all [feeds,wire]
  · refine ⟨(j,true),rfl,right,?_⟩
    rintro ⟨k,b⟩ h
    have k := feeds_reader L h
    rw [only] at k
    obtain rfl := List.mem_singleton.mp k
    cases b <;> simp_all [feeds,wire]

theorem unmarked_step (minim : LexMinimum n C) (i : Id C) (off : ¬boundary (n:=n) i) :
    ∃ p : Id C × Bool, feeds L i p ∧ i<p.1 ∧ ∀ r,feeds L i r → r=p := by
  have out : C.output≠n+i.val := fun e => off (Or.inl e)
  have live := live_slots L minim i out
  have cap : ¬2≤(readers C (n+i.val)).length := fun h => off (Or.inr h)
  obtain ⟨j,hj⟩ : ∃ j,readers C (n+i.val)=[j] := by
    cases e : readers C (n+i.val) with
    | nil => simp [e] at live
    | cons j tail => cases tail with
      | nil => exact ⟨j,rfl⟩
      | cons k ks => simp [e] at cap
  obtain ⟨p,_,hp,uniq⟩ := sole_pin L hj
  exact ⟨p,hp,feeds_later L hp,uniq⟩

/-- The trace retains the concrete reader side at each nonmarked gate. -/
noncomputable def trace (minim : LexMinimum n C) (i : Id C) : List (Id C × Bool) × Id C := by
  classical
  by_cases b : boundary (n:=n) i
  · exact ([],i)
  · let choice := unmarked_step L minim i b
    let p := choice.choose
    let tail := trace minim p.1
    exact (p::tail.1,tail.2)
termination_by C.gates.length-i.val
decreasing_by
  have lt := choice.choose_spec.2.1
  have cap := p.1.isLt
  change C.gates.length-p.1.val < C.gates.length-i.val
  change i.val < p.1.val at lt
  omega

noncomputable def column (minim : LexMinimum n C) (i : Id C) := (trace L minim i).2

theorem column_of_boundary (minim : LexMinimum n C) (i : Id C) (b : boundary (n:=n) i) :
    column L minim i=i := by unfold column; rw [trace]; simp [b]

theorem column_of_feed (minim : LexMinimum n C) (i : Id C) (p : Id C × Bool)
    (unmarked : ¬boundary (n:=n) i) (edge : feeds L i p) :
    column L minim i=column L minim p.1 := by
  have same := (unmarked_step L minim i unmarked).choose_spec.2.2 p edge
  unfold column
  conv_lhs => rw [trace]
  simp only [dif_neg unmarked, same]

inductive Walk : Id C → List (Id C × Bool) → Id C → Prop where
  | nil (i) : Walk i [] i
  | cons {i p ps q} (edge : feeds L i p) (rest : Walk p.1 ps q) : Walk i (p::ps) q

theorem trace_ok (minim : LexMinimum n C) (i : Id C) :
    Walk L i (trace L minim i).1 (column L minim i) ∧ boundary (n:=n) (column L minim i) := by
  by_cases b : boundary (n:=n) i
  · rw [column_of_boundary L minim i b,trace]
    simp only [dif_pos b]
    exact ⟨.nil i,b⟩
  · let ch := unmarked_step L minim i b
    let p := ch.choose
    have tail := trace_ok minim p.1
    rw [column_of_feed L minim i p b ch.choose_spec.1,trace]
    simp only [dif_neg b]
    exact ⟨.cons ch.choose_spec.1 tail.1,tail.2⟩
termination_by C.gates.length-i.val
decreasing_by
  have lt := ch.choose_spec.2.1
  have cap := p.1.isLt
  change C.gates.length-p.1.val < C.gates.length-i.val
  change i.val < p.1.val at lt
  omega

/-- Every walk to a marked gate hits the first boundary of its start,
before it can use any later fanout. Includes the zero-length walk. -/
theorem dominates (minim : LexMinimum n C) {i q : Id C} {ps} (path : Walk L i ps q)
    (endmark : boundary (n:=n) q) :
    column L minim i=i ∨ column L minim i∈ps.map Prod.fst := by
  induction path with
  | nil i => exact Or.inl (column_of_boundary L minim i endmark)
  | @cons i p ps q edge path ih =>
    by_cases b : boundary (n:=n) i
    · exact Or.inl (column_of_boundary L minim i b)
    · right
      rw [column_of_feed L minim i p b edge]
      simpa using ih endmark

theorem keep_shared (minim : LexMinimum n C) (i : Id C) (h : 2≤(readers C (n+i.val)).length) :
    column L minim i=i := column_of_boundary L minim i (Or.inr h)

noncomputable def effective (minim : LexMinimum n C) (r : Id C) :=
  (ThresholdSecondaryReceivers.signature C n r).image (column L minim)

theorem column_owner (minim : LexMinimum n C) (i : Id C) :
    column L minim i=column L minim (owner C n i) := by
  cases e : next C n i with
  | none => rw [owner_of_stop C n i e]
  | some j =>
    have one := next_readers e
    have notOut : C.output≠n+i.val := by
      intro eq
      have none : next C n i=none := by simp [next,one,eq]
      rw [none] at e
      contradiction
    have off : ¬boundary (n:=n) i := by simp [boundary,notOut,one]
    obtain ⟨p,toNode,edge,uniq⟩ := sole_pin L one
    rw [owner_of_next C n i j e,column_of_feed L minim i p off edge,toNode]
    exact column_owner minim j.val
termination_by C.gates.length-i.val
decreasing_by have cap := j.val.isLt; have lt := j.property; change i.val < j.val.val at lt; omega

/-- A wire path leaving a selected row and reaching any marked boundary
passes an effective column of that row.  This applies irrespective of gate
types on the private chain after its first flattened OR receiver. -/
theorem effective_cut (minim : LexMinimum n C) {r q : Id C} {p ps}
    (edge : feeds L r p) (tail : Walk L p.1 ps q) (endmark : boundary (n:=n) q) :
    ∃ v∈effective L minim r,v∈(p::ps).map Prod.fst := by
  let a := owner C n p.1
  have src : a∈ThresholdSecondaryReceivers.signature C n r := List.mem_toFinset.mpr
    (List.mem_map.mpr ⟨p.1,feeds_reader L edge,rfl⟩)
  have eq := column_owner L minim p.1
  have path := dominates L minim tail endmark
  refine ⟨column L minim p.1,Finset.mem_image.mpr ⟨a,src,eq.symm⟩,?_⟩
  simpa using path

end ThresholdEffectiveColumns
