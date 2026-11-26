import Research.CrownGateCounts

/-! Off-diagonal cell charging when distinct OR gates have disjoint diagonal supports. -/

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private theorem true_occurs {xs : List Bool} {i : ℕ} (hi : xs.getD i false = true) :
    true ∈ xs := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons a xs ih =>
    cases i with
    | zero => exact List.mem_cons.mpr (Or.inl (by simpa only [List.getD_cons_zero] using hi.symm))
    | succ i => exact List.mem_cons.mpr (Or.inr (ih (by simpa only [List.getD_cons_succ] using hi)))

theorem flag_index_unique {xs : List Bool} (budget : xs.count true ≤ 1)
    (k l : ℕ) (hk : xs.getD k false = true) (hl : xs.getD l false = true) : k = l := by
  induction xs generalizing k l with
  | nil => simp at hk
  | cons a xs ih =>
    cases a with
    | false =>
      have htail : xs.count true ≤ 1 := by simpa [List.count_cons] using budget
      cases k <;> cases l <;> simp only [List.getD_cons_zero,List.getD_cons_succ] at hk hl
      all_goals first | contradiction | exact congrArg Nat.succ (ih htail _ _ hk hl)
    | true =>
      have hz : xs.count true = 0 := by simp at budget; omega
      have hn := List.count_eq_zero.mp hz
      cases k <;> cases l <;> simp only [List.getD_cons_zero,List.getD_cons_succ] at hk hl
      all_goals first | rfl | exact False.elim (hn (true_occurs hk)) | exact False.elim (hn (true_occurs hl))

/-- The baseline inputs on which the gate at chronological index k is a true OR.
Positions after the last gate have empty support. -/
def orMarker {I : Type*} (gs : List Gate) (w : I → List Bool) (k : ℕ) : Set I :=
  {i | (trueOrFlags gs (w i)).getD k false = true}

theorem orMarker_pairwise {I : Type*} (gs : List Gate) (w : I → List Bool)
    (budget : ∀ i, (trueOrFlags gs (w i)).count true ≤ 1) :
    Pairwise (fun k l : ℕ => Disjoint (orMarker gs w k) (orMarker gs w l)) := by
  intro k l hkl
  apply Set.disjoint_left.mpr
  intro i hk hl
  exact hkl (flag_index_unique (budget i) k l hk hl)

theorem crown_orMarker_pairwise (C : Circuit) (hm : Monotone2 C)
    (hr : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (bound : (C.gates.filter isOrGate).length ≤ 22) :
    Pairwise (fun k l : ℕ =>
      Disjoint (orMarker C.gates (fun i : Fin 12 => oneEach i i) k)
        (orMarker C.gates (fun i : Fin 12 => oneEach i i) l)) :=
  orMarker_pairwise _ _ (fun i => crown_at_most_one_true_or i C hm hr bound)

theorem orMarker_head {I : Type*} (g : Gate) (gs : List Gate) (w : I → List Bool) :
    orMarker (g :: gs) w 0 =
      {i | isOrGate g = true ∧ g.op.eval (g.inputs.map fun j => (w i).getD j false) = true} := by
  ext i
  simp only [orMarker,Set.mem_ofPred_eq,trueOrFlags,List.getD_cons_zero,Bool.and_eq_true]

theorem orMarker_tail {I : Type*} (g : Gate) (gs : List Gate) (w : I → List Bool) (k : ℕ) :
    orMarker (g :: gs) w (k+1) = orMarker gs (fun i => advance g (w i)) k := by
  ext i
  simp only [orMarker,Set.mem_ofPred_eq,trueOrFlags,List.getD_cons_succ]

end PEqualNP.Research.MissingCell

namespace CrownDiagonalCharge
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]
abbrev CellSet (α : Type*) := Finset (Cell α)
abbrev WirePair (α : Type*) := CellSet α × CellSet α
noncomputable def trim (a c : CellSet α) : CellSet α :=
  if diagFree (a : Support α) then ∅ else c
def SmallDNF (a : CellSet α) : Prop :=
  ∃ t : Finset (RawTerm α), t.card ≤ 2 ∧ a = dnfCells t
def Approximates (S : CellSet α) (w : WirePair α) : Prop :=
  w.2 ⊆ w.1 ∧ w.1 ⊆ w.2 ∪ S ∧ (diagFree (w.1 : Support α) → w.2 = ∅)
omit [Fintype α] in
theorem approximates_mono {w : WirePair α} {S T : CellSet α} (h : Approximates S w)
    (hs : S ⊆ T) : Approximates T w :=
  ⟨h.1,h.2.1.trans (Finset.union_subset_union_right hs),h.2.2⟩
omit [Fintype α] in
theorem trim_or {S : CellSet α} (x y : WirePair α)
    (hx : Approximates S x) (hy : Approximates S y) :
    Approximates S (x.1 ∪ y.1, trim (x.1 ∪ y.1) (x.2 ∪ y.2)) := by
  classical
  by_cases h : diagFree ((x.1 ∪ y.1 : CellSet α) : Support α)
  · have xz := hx.2.2 (fun i hp => h i (Finset.mem_union_left _ hp))
    have yz := hy.2.2 (fun i hp => h i (Finset.mem_union_right _ hp))
    have ax := hx.2.1
    have ay := hy.2.1
    simp [xz] at ax
    simp [yz] at ay
    unfold Approximates
    dsimp only
    rw [trim,ite_eq_left h,Finset.empty_union]
    exact ⟨Finset.empty_subset _,Finset.union_subset ax ay,fun _ => rfl⟩
  · simp only [Approximates,trim,h,ite_false,false_implies,and_true]
    refine ⟨Finset.union_subset_union hx.1 hy.1,?_⟩
    intro i hi
    rcases Finset.mem_union.mp hi with hx'|hy'
    · have := hx.2.1 hx'
      grind
    · have := hy.2.1 hy'
      grind
theorem trim_and {S : CellSet α} (x y : WirePair α)
    (hx : Approximates S x) (hy : Approximates S y)
    (sx : SmallDNF x.2) (sy : SmallDNF y.2) :
    ∃ T : CellSet α, S ⊆ T ∧ T.card ≤ S.card + 4 ∧
    Approximates T (x.1 ∩ y.1, trim (x.1 ∩ y.1) (x.2 ∩ y.2)) := by
  classical
  have low := Finset.inter_subset_inter hx.1 hy.1
  have high : x.1 ∩ y.1 ⊆ (x.2 ∩ y.2) ∪ S := by
    intro p hp
    have a := hx.2.1 (Finset.mem_inter.mp hp).1
    have b := hy.2.1 (Finset.mem_inter.mp hp).2
    grind
  by_cases h : diagFree ((x.1 ∩ y.1 : CellSet α) : Support α)
  · refine ⟨S ∪ (x.2 ∩ y.2),Finset.subset_union_left,?_,?_⟩
    · obtain ⟨a,ha,ea⟩ := sx
      obtain ⟨b,hb,eb⟩ := sy
      have hz : diagFree ((x.2 ∩ y.2 : CellSet α) : Support α) := fun i hi => h i (low hi)
      rw [ea,eb] at hz ⊢
      exact two_term_empty_and_charge a b S ha hb hz
    · unfold Approximates
      dsimp only
      rw [trim,ite_eq_left h,Finset.empty_union]
      exact ⟨Finset.empty_subset _,by simpa only [Finset.union_comm S] using high,fun _ => rfl⟩
  · refine ⟨S,fun _ hp => hp,by omega,?_⟩
    unfold Approximates
    dsimp only
    rw [trim,ite_eq_right h]
    exact ⟨low,high,fun hh => False.elim (h hh)⟩
inductive PayTrace (α : Type*) [Fintype α] [DecidableEq α] : Set (WirePair α) → ℕ → Prop
  | start : PayTrace α {w | Approximates ∅ w} 0
  | union {K m x y} (prev : PayTrace α K m) (hx : x ∈ K) (hy : y ∈ K) :
      PayTrace α (insert (x.1 ∪ y.1, trim (x.1 ∪ y.1) (x.2 ∪ y.2)) K) m
  | inter {K m x y} (prev : PayTrace α K m) (hx : x ∈ K) (hy : y ∈ K)
      (sx : SmallDNF x.2) (sy : SmallDNF y.2) :
      PayTrace α (insert (x.1 ∩ y.1, trim (x.1 ∩ y.1) (x.2 ∩ y.2)) K) (m+1)
theorem pay_trace_bound {K : Set (WirePair α)} {m : ℕ} (tr : PayTrace α K m) :
    ∃ S : CellSet α, S.card ≤ 4*m ∧ ∀ w ∈ K, Approximates S w := by
  induction tr with
  | start => exact ⟨∅,by simp,fun _ h => h⟩
  | union prev hx hy ih =>
    obtain ⟨S,hc,hK⟩ := ih
    refine ⟨S,hc,?_⟩
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | old
    · exact trim_or _ _ (hK _ hx) (hK _ hy)
    · exact hK _ old
  | inter prev hx hy sx sy ih =>
    obtain ⟨S,hc,hK⟩ := ih
    obtain ⟨T,hs,ht,hp⟩ := trim_and _ _ (hK _ hx) (hK _ hy) sx sy
    refine ⟨T,by omega,?_⟩
    intro w hw
    rcases Set.mem_insert_iff.mp hw with rfl | old
    · exact hp
    · exact approximates_mono (hK _ old) hs
theorem pay_trace_crown {n m : ℕ} {K : Set (WirePair (Fin n))} (tr : PayTrace (Fin n) K m)
    {w : WirePair (Fin n)} (hw : w ∈ K) (ho : w.1 = Finset.univ.offDiag) :
    n*(n-1) ≤ 4*m := by
  obtain ⟨S,hc,hK⟩ := pay_trace_bound tr
  have hh := hK w hw
  have hz : diagFree (w.1 : Support (Fin n)) := by
    intro i hi
    rw [ho] at hi
    exact (Finset.mem_offDiag.mp hi).2.2 rfl
  have sub := hh.2.1
  rw [hh.2.2 hz,Finset.empty_union,ho] at sub
  have hh' := (Finset.card_le_card sub).trans hc
  simpa [Finset.offDiag_card,Nat.mul_sub] using hh'

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]
def diagIdx (a : Finset (Cell α)) : Finset α := Finset.univ.filter (fun i => (i,i) ∈ a)
def mergeTerm (a b : RawTerm α) : RawTerm α := (a.1 ∪ b.1, a.2 ∪ b.2)
theorem termCells_merge (a b : RawTerm α) :
    termCells (mergeTerm a b) = termCells a ∩ termCells b := by
  ext p
  simp [termCells,mergeTerm,←conj_inter]
def MarkNormal (M : Set (Finset (Cell α))) (w : Finset (Cell α)) : Prop :=
  w = ∅ ∨ ((diagIdx w).Nonempty ∧ ∃ t : RawTerm α,
    w = termCells t ∨ ∃ h ∈ M, w = termCells t ∩ h)

theorem and_normal {M : Set (Finset (Cell α))} {a b : Finset (Cell α)}
    (separate : ∀ h ∈ M, ∀ k ∈ M, h ≠ k → Disjoint (diagIdx h) (diagIdx k))
    (ha : MarkNormal M a) (hb : MarkNormal M b) (hl : (diagIdx (a ∩ b)).Nonempty) :
    MarkNormal M (a ∩ b) := by
  classical
  rcases ha with rfl | ⟨_,x,hx⟩
  · simp [diagIdx] at hl
  rcases hb with rfl | ⟨_,y,hy⟩
  · simp [diagIdx] at hl
  refine Or.inr ⟨hl, mergeTerm x y, ?_⟩
  rw [termCells_merge]
  rcases hx with rfl | ⟨h,hh,rfl⟩ <;> rcases hy with rfl | ⟨k,hk,rfl⟩
  · exact Or.inl rfl
  · exact Or.inr ⟨k,hk,by ext; simp⟩
  · exact Or.inr ⟨h,hh,by ext; simp [and_left_comm,and_comm]⟩
  · obtain ⟨i,hi⟩ := hl
    have both : i ∈ diagIdx h ∧ i ∈ diagIdx k := by
      simp only [diagIdx,Finset.mem_filter,Finset.mem_univ,true_and,Finset.mem_inter] at hi ⊢
      exact ⟨hi.1.2,hi.2.2⟩
    have eq : h=k := by
      by_contra hn
      exact Finset.disjoint_left.mp (separate h hh k hk hn) both.1 both.2
    subst k
    exact Or.inr ⟨h,hh,by ext; simp [and_left_comm,and_comm]⟩

theorem parent_pure {M : Set (Finset (Cell α))} {a out : Finset (Cell α)}
    (ha : MarkNormal M a) (hs : a ⊆ out)
    (fresh : ∀ h ∈ M, Disjoint (diagIdx out) (diagIdx h)) :
    a = ∅ ∨ ∃ t : RawTerm α, a = termCells t := by
  rcases ha with z | ⟨⟨i,hi⟩,t,ht | ⟨h,hh,eq⟩⟩
  · exact Or.inl z
  · exact Or.inr ⟨t,ht⟩
  · have mem := (Finset.mem_filter.mp hi).2
    have ho : i ∈ diagIdx out := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hs mem⟩
    rw [eq] at mem
    have hh' : i ∈ diagIdx h := Finset.mem_filter.mpr ⟨Finset.mem_univ _,(Finset.mem_inter.mp mem).2⟩
    exact False.elim (Finset.disjoint_left.mp (fresh h hh) ho hh')

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem empty_small : SmallDNF (∅ : CellSet α) := ⟨∅,by simp,by simp [dnfCells]⟩
theorem raw_small (t : RawTerm α) : SmallDNF (termCells t) :=
  ⟨{t},by simp,by simp [dnfCells]⟩

theorem intersect_raw_small (r : RawTerm α) {s : CellSet α} (hs : SmallDNF s) :
    SmallDNF (termCells r ∩ s) := by
  classical
  rcases hs with ⟨ts,hc,rfl⟩
  refine ⟨ts.image (mergeTerm r),Finset.card_image_le.trans hc,?_⟩
  ext p
  simp only [dnfCells,Finset.mem_inter,Finset.mem_biUnion,Finset.mem_image]
  constructor
  · rintro ⟨hr,t,ht,hp⟩
    exact ⟨_,⟨t,ht,rfl⟩,termCells_merge r t ▸ Finset.mem_inter.mpr ⟨hr,hp⟩⟩
  · rintro ⟨_,⟨t,ht,rfl⟩,hp⟩
    rw [termCells_merge] at hp
    exact ⟨(Finset.mem_inter.mp hp).1,t,ht,(Finset.mem_inter.mp hp).2⟩

theorem normal_small {M : Set (CellSet α)} {a : CellSet α}
    (hm : ∀ h ∈ M, SmallDNF h) (ha : MarkNormal M a) : SmallDNF a := by
  rcases ha with rfl | ⟨_,t,rfl | ⟨h,hh,rfl⟩⟩
  · exact empty_small
  · exact raw_small t
  · exact intersect_raw_small t (hm h hh)

theorem or_small {M : Set (CellSet α)} {a b : CellSet α}
    (ha : MarkNormal M a) (hb : MarkNormal M b)
    (fresh : ∀ h ∈ M, Disjoint (diagIdx (a ∪ b)) (diagIdx h)) :
    SmallDNF (a ∪ b) := by
  rcases parent_pure ha Finset.subset_union_left fresh with rfl | ⟨t,rfl⟩ <;>
    rcases parent_pure hb Finset.subset_union_right fresh with rfl | ⟨s,rfl⟩
  · simpa using (empty_small (α := α))
  · simpa using raw_small s
  · simpa using raw_small t
  · refine ⟨{t,s},Finset.card_insert_le .. |>.trans (by simp),by simp [dnfCells]⟩

theorem mark_or {M : Set (CellSet α)} {a : CellSet α} (live : (diagIdx a).Nonempty) :
    MarkNormal (insert a M) a := by
  refine Or.inr ⟨live,(∅,∅),Or.inr ⟨a,Set.mem_insert ..,?_⟩⟩
  ext p
  simp [termCells,conjSupport]

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]
noncomputable def plusW (x y : WirePair α) : WirePair α :=
  (x.1 ∪ y.1,trim (x.1 ∪ y.1) (x.2 ∪ y.2))
noncomputable def timesW (x y : WirePair α) : WirePair α :=
  (x.1 ∩ y.1,trim (x.1 ∩ y.1) (x.2 ∩ y.2))

inductive MarkerTrace (α : Type*) [Fintype α] [DecidableEq α] :
    Set (WirePair α) → Set (CellSet α) → ℕ → Prop
  | start : MarkerTrace α {w | w.1 = w.2 ∧ MarkNormal ∅ w.2} ∅ 0
  | union {K M m x y} (prev : MarkerTrace α K M m) (hx : x ∈ K) (hy : y ∈ K)
      (fresh : ∀ h ∈ M, Disjoint (diagIdx (x.1 ∪ y.1)) (diagIdx h)) :
      MarkerTrace α (insert (plusW x y) K) (insert (plusW x y).2 M) m
  | inter {K M m x y} (prev : MarkerTrace α K M m) (hx : x ∈ K) (hy : y ∈ K) :
      MarkerTrace α (insert (timesW x y) K) M (m+1)

theorem diag_trim {a b : CellSet α} (h : diagIdx a = diagIdx b) :
    diagIdx (trim a b) = diagIdx a := by
  classical
  by_cases hz : diagFree (a : Support α)
  · have zz : diagIdx a = ∅ := by
      ext i
      have hh : (i,i) ∉ a := hz i
      simp [diagIdx,hh]
    rw [trim,ite_eq_left hz,zz]
    simp [diagIdx]
  · rw [trim,ite_eq_right hz,h]
theorem diag_union (a b : CellSet α) : diagIdx (a ∪ b) = diagIdx a ∪ diagIdx b := by
  ext; simp [diagIdx]
theorem diag_inter (a b : CellSet α) : diagIdx (a ∩ b) = diagIdx a ∩ diagIdx b := by
  ext; simp [diagIdx]
theorem live_iff {a : CellSet α} : (diagIdx a).Nonempty ↔ ¬diagFree (a : Support α) := by
  classical
  simp [diagIdx,Finset.Nonempty,diagFree]
theorem normal_mono {M N : Set (CellSet α)} (sub : M ⊆ N) {x : CellSet α}
    (hx : MarkNormal M x) : MarkNormal N x := by
  rcases hx with z | ⟨l,t,h | ⟨g,hg,eq⟩⟩
  · exact Or.inl z
  · exact Or.inr ⟨l,t,Or.inl h⟩
  · exact Or.inr ⟨l,t,Or.inr ⟨g,sub hg,eq⟩⟩

structure Prefix (K : Set (WirePair α)) (M : Set (CellSet α)) (m : ℕ) : Prop where
  paid : ∃ J : Set (WirePair α), PayTrace α J m ∧ K ⊆ J
  same : ∀ w ∈ K, diagIdx w.1 = diagIdx w.2
  normals : ∀ w ∈ K, MarkNormal M w.2
  small : ∀ h ∈ M, SmallDNF h
  sep : ∀ h ∈ M, ∀ k ∈ M, h ≠ k → Disjoint (diagIdx h) (diagIdx k)

theorem marker_bound {K : Set (WirePair α)} {M m} (h : MarkerTrace α K M m) :
    Prefix K M m := by
  classical
  induction h with
  | start =>
    refine ⟨⟨_,PayTrace.start,?_⟩,fun w hw => congrArg diagIdx hw.1,fun w hw => hw.2,
      by simp,by simp⟩
    intro w hw
    obtain ⟨eq,norm⟩ := hw
    change Approximates ∅ w
    rw [show w = (w.2,w.2) by exact Prod.ext eq rfl]
    refine ⟨fun _ a => a,by simp,?_⟩
    intro hz
    rcases norm with z | ⟨live,_⟩
    · exact z
    · exact False.elim (live_iff.mp live hz)
  | @union K M m x y prev hx hy fresh ih =>
    let z := plusW x y
    have e : diagIdx (x.1 ∪ y.1) = diagIdx (x.2 ∪ y.2) := by
      rw [diag_union,diag_union,ih.same x hx,ih.same y hy]
    have same : diagIdx z.2 = diagIdx z.1 := diag_trim e
    have sm : SmallDNF z.2 := by
      change SmallDNF (trim (x.1 ∪ y.1) (x.2 ∪ y.2))
      by_cases h : diagFree ((x.1 ∪ y.1 : CellSet α) : Support α)
      · rw [trim,ite_eq_left h]; exact empty_small
      · rw [trim,ite_eq_right h]
        exact or_small (ih.normals _ hx) (ih.normals _ hy) (e ▸ fresh)
    have fr : ∀ h ∈ M, Disjoint (diagIdx z.2) (diagIdx h) := by
      rw [same]; exact fresh
    obtain ⟨J,tr,sub⟩ := ih.paid
    refine ⟨⟨_,PayTrace.union tr (sub hx) (sub hy),Set.insert_subset_insert sub⟩,?_,?_,?_,?_⟩
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | old
      · exact same.symm
      · exact ih.same _ old
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | old
      · by_cases hz : diagFree (z.1 : Support α)
        · exact Or.inl (ite_eq_left hz : z.2 = ∅)
        · exact mark_or (live_iff.mpr (fun hd => hz (by
            by_contra hh
            have := live_iff.mpr hh
            rw [←same] at this
            exact live_iff.mp this hd)))
      · exact normal_mono (Set.subset_insert ..) (ih.normals _ old)
    · intro a ha
      rcases Set.mem_insert_iff.mp ha with rfl | old
      · exact sm
      · exact ih.small _ old
    · intro a ha b hb ne
      rcases Set.mem_insert_iff.mp ha with rfl | old <;> rcases Set.mem_insert_iff.mp hb with rfl | old'
      · exact False.elim (ne rfl)
      · exact fr _ old'
      · exact (fr _ old).symm
      · exact ih.sep _ old _ old' ne
  | @inter K M m x y prev hx hy ih =>
    let z := timesW x y
    have e : diagIdx (x.1 ∩ y.1) = diagIdx (x.2 ∩ y.2) := by
      rw [diag_inter,diag_inter,ih.same x hx,ih.same y hy]
    have same : diagIdx z.2 = diagIdx z.1 := diag_trim e
    obtain ⟨J,tr,sub⟩ := ih.paid
    refine ⟨⟨_,PayTrace.inter tr (sub hx) (sub hy)
      (normal_small ih.small (ih.normals _ hx)) (normal_small ih.small (ih.normals _ hy)),
      Set.insert_subset_insert sub⟩,?_,?_,ih.small,ih.sep⟩
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | old
      · exact same.symm
      · exact ih.same _ old
    · intro w hw
      rcases Set.mem_insert_iff.mp hw with rfl | old
      · by_cases hz : diagFree (z.1 : Support α)
        · exact Or.inl (ite_eq_left hz : z.2 = ∅)
        · have live : (diagIdx (x.2 ∩ y.2)).Nonempty := e ▸ live_iff.mpr hz
          change MarkNormal M (trim z.1 (x.2 ∩ y.2))
          rw [trim,ite_eq_right hz]
          exact and_normal ih.sep (ih.normals _ hx) (ih.normals _ hy) live
      · exact ih.normals _ old

theorem marker_trace_crown {n m : ℕ} {K : Set (WirePair (Fin n))} {M}
    (tr : MarkerTrace (Fin n) K M m) {w : WirePair (Fin n)} (hw : w ∈ K)
    (ho : w.1 = Finset.univ.offDiag) : n*(n-1) ≤ 4*m := by
  obtain ⟨J,tr,sub⟩ := (marker_bound tr).paid
  exact pay_trace_crown tr (sub hw) ho
end CrownDiagonalCharge

namespace CrownDiagonalCharge
open scoped Classical
variable {α : Type*} [Fintype α] [DecidableEq α]

theorem initial_normal (a : Finset (Cell α)) (h : Charged ∅ (a : Support α)) :
    MarkNormal ∅ a := by
  classical
  rcases h with ⟨r,c,he,hn⟩ | hz
  · refine Or.inr ⟨?_,(r,c),Or.inl ?_⟩
    · by_contra h
      apply hn
      intro i hi
      exact h ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
    · ext p
      change p ∈ (a : Support α) ↔ _
      rw [he]
      simp [termCells]
  · exact Or.inl (Finset.eq_empty_iff_forall_notMem.mpr (fun i hi => Finset.notMem_empty i (hz hi)))

noncomputable def supportCells (A : Support α) : Finset (Cell α) := A.toFinset
omit [DecidableEq α] in
theorem coe_supportCells (A : Support α) : (supportCells A : Support α) = A := by
  simp [supportCells]

theorem initial_fin_normal (A : Support α) (h : Charged ∅ A) :
    MarkNormal ∅ (supportCells A) := initial_normal _ (by rw [coe_supportCells]; exact h)

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds
open scoped Classical
variable {n : ℕ}

def Actual (K : Set (WirePair (Fin n))) : Set (Support (Fin n)) :=
  {A | ∃ w ∈ K, (w.1 : Support (Fin n)) = A}

theorem actual_mono {K J : Set (WirePair (Fin n))} (h : K ⊆ J) :
    Actual K ⊆ Actual J := by
  rintro A ⟨w,hw,rfl⟩
  exact ⟨w,h hw,rfl⟩

theorem marker_gate_args {K : Set (WirePair (Fin n))} (w : Env n) (g : Gate)
    (hw : ∀ i, wire w i ∈ Actual K) (h0 : ∅ ∈ Actual K) (h1 : Set.univ ∈ Actual K)
    (len : g.inputs.length ≤ 2) (hop : g.op = .and ∨ g.op = .or) :
    ∃ x ∈ K, ∃ y ∈ K,
      (g.op = .and → ((timesW x y).1 : Support (Fin n)) = gateSupport g w) ∧
      (g.op = .or → ((plusW x y).1 : Support (Fin n)) = gateSupport g w) := by
  obtain ⟨A,⟨x,hx,rfl⟩,B,⟨y,hy,rfl⟩,ha,ho⟩ := gate_args w g hw h0 h1 len hop
  exact ⟨x,hx,y,hy,fun h => by simpa [timesW] using (ha h).symm,
    fun h => by simpa [plusW] using (ho h).symm⟩

theorem marker_or_diag {K : Set (WirePair (Fin n))} {M m} (tr : MarkerTrace (Fin n) K M m)
    {x y : WirePair (Fin n)} (hx : x ∈ K) (hy : y ∈ K) :
    diagIdx (plusW x y).2 = diagIdx (plusW x y).1 := by
  apply diag_trim
  rw [diag_union,diag_union,(marker_bound tr).same x hx,(marker_bound tr).same y hy]

end CrownDiagonalCharge

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell
open scoped Classical

def diagonalMarker {n : ℕ} (gs : List Gate) (w : Env n) (k : ℕ) : Set (Fin n) :=
  orMarker gs (fun i => w (i,i)) k

private theorem marker_succ {n : ℕ} (g : Gate) (gs : List Gate) (w : Env n) (k : ℕ) :
    diagonalMarker (g :: gs) w (k+1) = diagonalMarker gs (push g w) k :=
  orMarker_tail g gs _ k

private theorem marker_head {n : ℕ} (g : Gate) (gs : List Gate) (w : Env n)
    (h : g.op = .or) (a : CellSet (Fin n)) (ha : (a : Support (Fin n)) = gateSupport g w) :
    (diagIdx a : Set (Fin n)) = diagonalMarker (g :: gs) w 0 := by
  ext i
  rw [diagonalMarker,orMarker_head]
  have he := Set.ext_iff.mp ha (i,i)
  simpa [diagIdx,isOrGate,h,gateSupport] using he

theorem marker_trace_eval {n : ℕ} (gs : List Gate) (w : Env n) (k m : ℕ)
    (K : Set (WirePair (Fin n))) (M : Set (CellSet (Fin n))) (tr : MarkerTrace (Fin n) K M m)
    (h0 : ∅ ∈ Actual K) (h1 : Set.univ ∈ Actual K) (hw : ∀ i, wire w i ∈ Actual K)
    (hl : ∀ p, (w p).length = k)
    (ha : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (sep : Pairwise (fun a b : ℕ => Disjoint (diagonalMarker gs w a) (diagonalMarker gs w b)))
    (past : ∀ d ∈ M, ∀ t, Disjoint (diagonalMarker gs w t) (diagIdx d : Set (Fin n))) :
    ∃ J N, MarkerTrace (Fin n) J N (m + (gs.filter isAndGate).length) ∧
      ∀ i, wire (fun p => (Circuit.mk gs i).wires (w p)) i ∈ Actual J := by
  induction gs generalizing w k m K M with
  | nil => exact ⟨K,M,by simpa using tr,hw⟩
  | cons g gs ih =>
    obtain ⟨hop,len⟩ := ha g (List.mem_cons_self ..)
    obtain ⟨x,hx,y,hy,han,hor⟩ := marker_gate_args w g hw h0 h1 len hop
    have sepn : Pairwise (fun a b : ℕ => Disjoint (diagonalMarker gs (push g w) a)
        (diagonalMarker gs (push g w) b)) := by
      intro a b hab
      rw [←marker_succ,←marker_succ]
      exact sep (fun he => hab (Nat.succ.inj he))
    have pastn : ∀ d ∈ M, ∀ t, Disjoint (diagonalMarker gs (push g w) t) (diagIdx d : Set (Fin n)) := by
      intro d hd t
      rw [←marker_succ]
      exact past d hd (t+1)
    have step : ∃ J N, MarkerTrace (Fin n) J N (m + (if isAndGate g then 1 else 0)) ∧
        K ⊆ J ∧ gateSupport g w ∈ Actual J ∧
        ∀ d ∈ N, ∀ t, Disjoint (diagonalMarker gs (push g w) t) (diagIdx d : Set (Fin n)) := by
      rcases hop with h | h
      · exact ⟨_,M, by simpa [isAndGate,h] using MarkerTrace.inter tr hx hy,
          Set.subset_insert .., ⟨_,Set.mem_insert ..,han h⟩, pastn⟩
      · have hd := marker_head g gs w h (plusW x y).1 (hor h)
        have fresh : ∀ d ∈ M, Disjoint (diagIdx (x.1 ∪ y.1)) (diagIdx d) := by
          intro d hm
          apply Finset.disjoint_left.mpr
          intro i hi hj
          apply Set.disjoint_left.mp (past d hm 0) _ hj
          rw [←hd]
          exact hi
        refine ⟨_,_, by simpa [isAndGate,h] using MarkerTrace.union tr hx hy fresh,
          Set.subset_insert .., ⟨_,Set.mem_insert ..,hor h⟩, ?_⟩
        intro d hm t
        rcases Set.mem_insert_iff.mp hm with rfl | hm
        · rw [marker_or_diag tr hx hy,hd,←marker_succ]
          exact sep (by omega : t+1 ≠ 0)
        · exact pastn _ hm t
    obtain ⟨J,N,tj,sub,gate,pnext⟩ := step
    have hn := push_known g hl (fun i => actual_mono sub (hw i)) gate
    have ln : ∀ p, (push g w p).length = k+1 := by intro p; simp [push,hl]
    obtain ⟨J',N',tj',hout⟩ := ih (push g w) (k+1) _ J N tj (actual_mono sub h0)
      (actual_mono sub h1) hn ln (fun a h => ha a (List.mem_cons_of_mem _ h)) sepn pnext
    refine ⟨J',N',?_,hout⟩
    cases h : isAndGate g <;> simpa [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tj'

theorem circuit_crown_four_and {n : ℕ} (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin n => decide (u ≠ v)) C)
    (sep : Pairwise (fun a b : ℕ => Disjoint
      (diagonalMarker C.gates (fun p : Cell (Fin n) => oneEach p.1 p.2) a)
      (diagonalMarker C.gates (fun p : Cell (Fin n) => oneEach p.1 p.2) b))) :
    n*(n-1) ≤ 4*(C.gates.filter isAndGate).length := by
  classical
  let w : Env n := fun p => oneEach p.1 p.2
  let K : Set (WirePair (Fin n)) := {v | v.1 = v.2 ∧ MarkNormal ∅ v.2}
  have init (A : Support (Fin n)) (ch : Charged ∅ A) : A ∈ Actual K :=
    ⟨(supportCells A,supportCells A), ⟨rfl,initial_fin_normal A ch⟩,coe_supportCells A⟩
  obtain ⟨J,N,tr,hw⟩ := marker_trace_eval C.gates w (n+n) 0 K ∅ MarkerTrace.start
    (init _ initial_false) (init _ initial_true) (fun i => init _ (initial_wire i))
    (fun p => by simp [w,oneEach]) hm sep (by simp)
  obtain ⟨v,hv,he⟩ := hw C.output
  have eq : v.1 = Finset.univ.offDiag := by
    ext p
    have hp := Set.ext_iff.mp he p
    change (p ∈ v.1) ↔ C.eval (oneEach p.1 p.2) = true at hp
    rw [rep p.1 p.2] at hp
    simpa using hp
  simpa using marker_trace_crown tr hv eq

theorem and_or_partition (gs : List Gate)
    (hm : ∀ g ∈ gs, g.op = .and ∨ g.op = .or) :
    (gs.filter isAndGate).length + (gs.filter isOrGate).length = gs.length := by
  induction gs with
  | nil => simp
  | cons g gs ih =>
    have ht := ih (fun a ha => hm a (List.mem_cons_of_mem _ ha))
    rcases hm g (List.mem_cons_self ..) with h | h <;>
      simp [isAndGate,isOrGate,h] <;> omega

theorem crown_size_forty_requires_twenty_three_ors (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) : 23 ≤ (C.gates.filter isOrGate).length := by
  by_contra! h
  have budget : (C.gates.filter isOrGate).length ≤ 22 := by omega
  have sep := crown_orMarker_pairwise C hm rep budget
  have bound := circuit_crown_four_and C hm rep sep
  have old := crown_twelve_or_count C hm rep
  have part := and_or_partition C.gates (fun g h => (hm g h).1)
  change C.gates.length ≤ 40 at size
  omega

end CrownDiagonalCharge
