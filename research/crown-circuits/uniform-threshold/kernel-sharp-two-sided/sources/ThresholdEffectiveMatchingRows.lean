import ThresholdFamilySimpleGraph
import ThresholdCodegreeRecords
import ThresholdWarmRetention
namespace ThresholdEffectiveMatchingRows
open scoped BigOperators
variable {I V : Type*} [DecidableEq I] [DecidableEq V]
def fiber (R : Finset I) (col : I → Finset V) (F : Finset V) :=
  (R.powersetCard 2).filter (fun p => p.biUnion col=F)
def matchings (E : Finset (Finset V)) (F : Finset V) :=
  (E.powersetCard 2).filter (fun m => m.biUnion id=F)

theorem edge_label (R : Finset I) (S : Finset V) (col : I → Finset V)
    (inj : Set.InjOn col (R:Set I)) (a b : ↥S)
    (adj : (ThresholdFamilySimpleGraph.graph S (R.image col)).Adj a b) :
    ∃! r : ↥R,col r.val={a.val,b.val} := by
  obtain ⟨r,hr,eq⟩ := Finset.mem_image.mp adj.2
  exact ⟨⟨r,hr⟩,eq,fun q hq => Subtype.ext (inj q.property hr (hq.trans eq.symm))⟩

noncomputable def matchingEquiv (R : Finset I) (col : I → Finset V)
    (inj : Set.InjOn col (R:Set I)) (F : Finset V) :
    ↥(fiber R col F) ≃ ↥(matchings (R.image col) F) := by
  classical
  let back := fun m : Finset (Finset V) => R.filter (fun r => col r∈m)
  have undo (p : Finset I) (sub : p⊆R) : back (p.image col)=p := by
    ext r
    constructor
    · intro h
      obtain ⟨hr,y⟩ := Finset.mem_filter.mp h
      obtain ⟨s,hs,eq⟩ := Finset.mem_image.mp y
      exact (inj (sub hs) hr eq) ▸ hs
    · intro h
      exact Finset.mem_filter.mpr ⟨sub h,Finset.mem_image_of_mem _ h⟩
  have redo (m : Finset (Finset V)) (sub : m⊆R.image col) : (back m).image col=m := by
    ext a
    constructor
    · intro h
      obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hr).2
    · intro h
      obtain ⟨r,hr,eq⟩ := Finset.mem_image.mp (sub h)
      exact Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,eq.symm ▸ h⟩,eq⟩
  have box (p : Finset I) : (p.image col).biUnion id=p.biUnion col := by
    ext; simp
  let f : ↥(fiber R col F) → ↥(matchings (R.image col) F) := fun p => by
    obtain ⟨pool,hb⟩ := Finset.mem_filter.mp p.property
    obtain ⟨sub,hc⟩ := Finset.mem_powersetCard.mp pool
    exact ⟨p.val.image col,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨Finset.image_subset_image sub,(Finset.card_image_of_injOn (inj.mono sub)).trans hc⟩,(box _).trans hb⟩⟩
  let g : ↥(matchings (R.image col) F) → ↥(fiber R col F) := fun m => by
    obtain ⟨pool,hb⟩ := Finset.mem_filter.mp m.property
    obtain ⟨sub,hc⟩ := Finset.mem_powersetCard.mp pool
    have restored := redo m.val sub
    have ss : back m.val⊆R := Finset.filter_subset _ _
    have cc := Finset.card_image_of_injOn (inj.mono ss)
    exact ⟨back m.val,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr
      ⟨ss,cc.symm.trans ((congrArg Finset.card restored).trans hc)⟩,
      (box _).symm.trans ((congrArg (fun e : Finset (Finset V) => e.biUnion id) restored).trans hb)⟩⟩
  exact ⟨f,g,fun p => Subtype.ext (undo _ (Finset.mem_powersetCard.mp
    (Finset.mem_filter.mp p.property).1).1),fun m => Subtype.ext (redo _
      (Finset.mem_powersetCard.mp (Finset.mem_filter.mp m.property).1).1)⟩

open ThresholdFourSetOccupancy ThresholdCodegreeRecords
def localEdges (x : Quad) : Finset (Finset (Fin 4)) :=
  (Finset.univ.powersetCard 2).filter (fun p =>
    ∀ i∈p,∀ j∈p,i≠j → edgeBit x i j=true)
theorem local_matching_card (x : Quad) :
    (matchings (localEdges x) Finset.univ).card=occupancy x := by
  obtain ⟨a,b,c,d,e,f⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

theorem induced_matching_card (R : Finset I) (col : I → Finset (Fin 4))
    (inj : Set.InjOn col (R:Set I)) (x : Quad)
    (induced : R.image col=localEdges x) :
    (fiber R col Finset.univ).card=occupancy x := by
  have eq := Fintype.card_congr (matchingEquiv R col inj Finset.univ)
  simpa [induced,local_matching_card] using eq


/-- Restrict to the induced four-set before reindexing its row endpoints. -/
def inside (R : Finset I) (col : I → Finset V) (f : Fin 4 ↪ V) :=
  R.filter (fun r => col r⊆Finset.univ.map f)
def pull (f : Fin 4 ↪ V) (p : Finset V) := Finset.univ.filter (fun i => f i∈p)
theorem restore (f : Fin 4 ↪ V) (p : Finset V) (sub : p⊆Finset.univ.map f) :
    (pull f p).map f=p := by
  ext a
  constructor
  · intro h; obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
    exact (Finset.mem_filter.mp hi).2
  · intro h; obtain ⟨i,_,hi⟩ := Finset.mem_map.mp (sub h)
    exact Finset.mem_map.mpr ⟨i,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi.symm ▸ h⟩,hi⟩

theorem chart_fiber (R : Finset I) (col : I → Finset V) (f : Fin 4 ↪ V) :
    fiber R col (Finset.univ.map f)=fiber (inside R col f) (fun r => pull f (col r)) Finset.univ := by
  ext p
  simp only [fiber,Finset.mem_filter,Finset.mem_powersetCard]
  constructor
  · rintro ⟨⟨sub,sz⟩,box⟩
    have within (r) (hr : r∈p) : col r⊆Finset.univ.map f := by
      intro a ha; rw [←box]; exact Finset.mem_biUnion.mpr ⟨r,hr,ha⟩
    refine ⟨⟨fun r hr => Finset.mem_filter.mpr ⟨sub hr,within r hr⟩,sz⟩,?_⟩
    ext i
    simp only [Finset.mem_univ,iff_true]
    have h : f i∈p.biUnion col := by rw [box]; simp
    obtain ⟨r,hr,hi⟩ := Finset.mem_biUnion.mp h
    exact Finset.mem_biUnion.mpr ⟨r,hr,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hi⟩⟩
  · rintro ⟨⟨sub,sz⟩,box⟩
    refine ⟨⟨fun r hr => (Finset.mem_filter.mp (sub hr)).1,sz⟩,?_⟩
    ext a
    constructor
    · intro h
      obtain ⟨r,hr,ha⟩ := Finset.mem_biUnion.mp h
      exact (Finset.mem_filter.mp (sub hr)).2 ha
    · intro h
      obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp h
      have hi : i∈p.biUnion (fun r => pull f (col r)) := by rw [box]; simp
      obtain ⟨r,hr,hp⟩ := Finset.mem_biUnion.mp hi
      exact Finset.mem_biUnion.mpr ⟨r,hr,(Finset.mem_filter.mp hp).2⟩
def familyQuad (E : Finset (Finset V)) (f : Fin 4 ↪ V) : Quad :=
  let e := fun i j : Fin 4 => decide ({f i,f j}∈E)
  ⟨e 0 1,e 2 3,e 0 2,e 1 3,e 0 3,e 1 2⟩

theorem family_bits (E : Finset (Finset V)) (f : Fin 4 ↪ V)
    (i j : Fin 4) (ne : i≠j) :
    edgeBit (familyQuad E f) i j=true ↔ {f i,f j}∈E := by
  fin_cases i <;> fin_cases j <;> simp_all [edgeBit,familyQuad,Finset.pair_comm] <;> rw [Finset.pair_comm (f 1) (f 0)]

theorem induced (R : Finset I) (col : I → Finset V) (f : Fin 4 ↪ V)
    (two : ∀ r∈R,(col r).card=2) :
    (inside R col f).image (fun r => pull f (col r))=localEdges (familyQuad (R.image col) f) := by
  ext p
  constructor
  · intro h
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
    obtain ⟨mem,inc⟩ := Finset.mem_filter.mp hr
    have restore' := restore f (col r) inc
    have card : (pull f (col r)).card=2 := by simpa using (congrArg Finset.card restore').trans (two r mem)
    refine Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,card⟩,?_⟩
    intro i hi j hj ne
    apply (family_bits _ _ _ _ ne).mpr
    apply Finset.mem_image.mpr
    refine ⟨r,mem,Eq.symm (Finset.eq_of_subset_of_card_le ?_ ?_)⟩
    · intro a ha
      simp only [Finset.mem_insert,Finset.mem_singleton] at ha
      rcases ha with rfl|rfl
      · exact (Finset.mem_filter.mp hi).2
      · exact (Finset.mem_filter.mp hj).2
    · simp [two r mem,f.injective.ne ne]
  · intro h
    obtain ⟨sz,edges⟩ := Finset.mem_filter.mp h
    obtain ⟨a,b,ne,eq⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp sz).2
    have edge := (family_bits _ _ a b ne).mp (edges a (by simp [eq]) b (by simp [eq]) ne)
    obtain ⟨r,hr,er⟩ := Finset.mem_image.mp edge
    have inc : col r⊆Finset.univ.map f := by
      rw [er]
      intro z hz
      simp only [Finset.mem_insert,Finset.mem_singleton] at hz
      rcases hz with rfl|rfl
      · exact Finset.mem_map.mpr ⟨a,Finset.mem_univ _,rfl⟩
      · exact Finset.mem_map.mpr ⟨b,Finset.mem_univ _,rfl⟩
    refine Finset.mem_image.mpr ⟨r,Finset.mem_filter.mpr ⟨hr,inc⟩,?_⟩
    ext i
    simp [pull,er,eq]

theorem occupancy_eq (R : Finset I) (col : I → Finset V) (f : Fin 4 ↪ V)
    (two : ∀ r∈R,(col r).card=2) (inj : Set.InjOn col (R:Set I)) :
    (fiber R col (Finset.univ.map f)).card=occupancy (familyQuad (R.image col) f) := by
  rw [chart_fiber]
  apply induced_matching_card _ _ _ _ (induced R col f two)
  intro a ha b hb eq
  obtain ⟨ar,asub⟩ := Finset.mem_filter.mp ha
  obtain ⟨br,bsub⟩ := Finset.mem_filter.mp hb
  exact inj ar br ((restore f _ asub).symm.trans ((congrArg (Finset.map f) eq).trans (restore f _ bsub)))

open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open T2OrPartition ThresholdRegularSource ThresholdOrExtraction ThresholdSimpleIncidence ThresholdEffectiveColumns
noncomputable def actualPool {C : Circuit} {n : Nat} (L : Layout C n) (R : Finset (Id C)) :=
  (R.powersetCard 2).filter (fun p => ∃ x : Fin n, endpoints L x=p)

theorem actual_iff {C : Circuit} {n : Nat} (L : Layout C n) (R : Finset (Id C))
    (p : Finset (Id C)) : p∈actualPool L R ↔ p⊆R ∧ p.card=2 ∧ ∃ x : Fin n,endpoints L x=p := by
  simp [actualPool,Finset.mem_powersetCard,and_assoc]

theorem effective_occupancy {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    (R : Finset (Id C)) (two : ∀ r∈R,(effective L M r).card=2)
    (inj : Set.InjOn (effective L M) (R:Set _)) (f : Fin 4 ↪ Id C) :
    (fiber R (effective L M) (Finset.univ.map f)).card=
      occupancy (familyQuad (R.image (effective L M)) f) :=
  occupancy_eq _ _ _ two inj
/-- The occupancy record uses exactly the same six graph adjacency bits as the
global diagonal-record count. Pass from the supported vertex subtype to the
actual column ID only on the row-pair side. -/
theorem graph_quad (S : Finset V) (E : Finset (Finset V)) (f : Fin 4 ↪ ↥S)
    [DecidableRel (ThresholdFamilySimpleGraph.graph S E).Adj] :
    familyQuad E (f.trans (Function.Embedding.subtype (·∈S))) =
    ofGraph (ThresholdFamilySimpleGraph.graph S E) (f 0) (f 1) (f 2) (f 3) := by
  simp [familyQuad,ofGraph,ThresholdFamilySimpleGraph.graph]

theorem box_graph (R : Finset I) (col : I → Finset V) (S : Finset V)
    (two : ∀ r∈R,(col r).card=2) (inj : Set.InjOn col (R:Set I))
    (f : Fin 4 ↪ ↥S) [DecidableRel (ThresholdFamilySimpleGraph.graph S (R.image col)).Adj] :
    (fiber R col (Finset.univ.map (f.trans (Function.Embedding.subtype (·∈S))))).card =
    occupancy (ofGraph (ThresholdFamilySimpleGraph.graph S (R.image col))
      (f 0) (f 1) (f 2) (f 3)) := by
  rw [occupancy_eq R col _ two inj,graph_quad]

end ThresholdEffectiveMatchingRows
