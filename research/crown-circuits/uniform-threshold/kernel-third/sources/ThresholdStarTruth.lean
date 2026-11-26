import ThresholdStarReindex
import ThresholdCoveredPins
import Research.WegenerThreshold
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity ThresholdOrGroups
open ThresholdStarReindex ThresholdPeelSchedule T2SoleOrSplice
namespace ThresholdStarTruth
-- Physical monotonicity proof from PEqualNP.Outside.L_meta_5533.
def step (w : List Bool) (g : Gate) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

def ExtendsBits (x y : List Bool) : Prop :=
  x.length = y.length ∧ ∀ i, x.getD i false = true → y.getD i false = true

theorem gate_map_mono (op : GateOp) (hop : op = GateOp.and ∨ op = GateOp.or)
    (ins : List ℕ) (x y : List Bool) (h : ExtendsBits x y) :
    op.eval (ins.map fun i => x.getD i false) = true →
      op.eval (ins.map fun i => y.getD i false) = true := by
  rcases hop with rfl | rfl
  · simp only [GateOp.eval, List.all_map, List.all_eq_true, Function.comp_apply, id_eq]
    exact fun hall i hi => h.2 i (hall i hi)
  · simp only [GateOp.eval, List.any_map, List.any_eq_true, Function.comp_apply, id_eq]
    rintro ⟨i, hi, ht⟩
    exact ⟨i, hi, h.2 i ht⟩

theorem getD_snoc (x : List Bool) (b : Bool) : (x ++ [b]).getD x.length false = b := by
  simp

theorem gate_step_mono (g : Gate) (hop : g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (h : ExtendsBits x y) : ExtendsBits (step x g) (step y g) := by
  refine ⟨by simp [step, h.1], ?_⟩
  intro i hi
  rcases lt_trichotomy i x.length with hlt | heq | hgt
  · rw [step, List.getD_append _ _ _ _ hlt] at hi
    rw [step, List.getD_append _ _ _ _ (by rw [← h.1]; exact hlt)]
    exact h.2 i hi
  · subst i
    rw [step, getD_snoc] at hi
    rw [h.1, step, getD_snoc]
    exact gate_map_mono g.op hop g.inputs x y h hi
  · rw [List.getD_eq_default _ _ (by simp [step]; omega)] at hi
    contradiction

theorem gates_mono (gs : List Gate) (hgs : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or)
    (x y : List Bool) (hxy : ExtendsBits x y) :
    ExtendsBits (gs.foldl step x) (gs.foldl step y) := by
  induction gs generalizing x y with
  | nil => exact hxy
  | cons g gs ih =>
    have ht : ∀ k ∈ gs, k.op = GateOp.and ∨ k.op = GateOp.or :=
      fun k hk => hgs k (List.mem_cons_of_mem _ hk)
    exact ih ht _ _ (gate_step_mono g (hgs g (by simp)) x y hxy)

theorem circuit_mono (C : Circuit) (hC : Monotone2 C) (x y : List Bool)
    (hxy : ExtendsBits x y) (hx : C.eval x = true) : C.eval y = true := by
  have hop g (hg : g ∈ C.gates) : g.op = GateOp.and ∨ g.op = GateOp.or := by
    simpa using (hC g hg).1
  exact (gates_mono C.gates hop x y hxy).2 C.output hx

noncomputable def assignment {m k} (center : Fin m) (neighbor : Fin k ↪ Fin m)
    (v : Fin m) : Port k := by
  classical
  exact if v=center then .fixed true else if h : ∃ i,neighbor i=v then .port h.choose else .fixed false

theorem assigned_row {m k} (center : Fin m) (neighbor : Fin k ↪ Fin m)
    (s : Finset (Fin k)) :
    List.ofFn (assigned (vector s) ∘ assignment center neighbor) =
      List.ofFn (row (insert center (s.map neighbor))) := by
  classical
  apply congrArg List.ofFn
  funext v
  by_cases eq : v=center
  · subst v; simp [assignment,assigned,row]
  · by_cases hit : ∃ i,neighbor i=v
    · have key : v∈s.map neighbor ↔ hit.choose∈s := by
        constructor
        · intro hv
          obtain ⟨i,hi,he⟩ := Finset.mem_map.mp hv
          have same := neighbor.injective (he.trans hit.choose_spec.symm)
          simpa [same] using hi
        · intro hi
          exact Finset.mem_map.mpr ⟨_,hi,hit.choose_spec⟩
      simp [assignment,eq,hit,assigned,vector,List.getD_eq_getElem?_getD,row,key]
    · have no : v∉s.map neighbor := by
        intro hv
        obtain ⟨i,_,he⟩ := Finset.mem_map.mp hv
        exact hit ⟨i,he⟩
      simp [assignment,eq,hit,assigned,row,no]

theorem covered_star {n m k} (center : Fin m) (neighbor : Fin k ↪ Fin m)
    (edge : Fin k ↪ Fin n) (ends : Fin n → Finset (Fin m))
    (shape : ∀ i,ends (edge i)={center,neighbor i}) (s : Finset (Fin k)) (hs : s.Nonempty) :
    covered ends (s.map edge)=insert center (s.map neighbor) := by
  classical
  ext v
  constructor
  · intro hv
    obtain ⟨j,hj,on⟩ := Finset.mem_biUnion.mp hv
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    rw [shape] at on
    rcases Finset.mem_insert.mp on with eq|other
    · exact Finset.mem_insert.mpr (Or.inl eq)
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_map.mpr ⟨i,hi,(Finset.mem_singleton.mp other).symm⟩))
  · intro hv
    rcases Finset.mem_insert.mp hv with eq|other
    · subst v
      obtain ⟨i,hi⟩ := hs
      exact Finset.mem_biUnion.mpr ⟨edge i,Finset.mem_map.mpr ⟨i,hi,rfl⟩,by simp [shape]⟩
    · obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp other
      exact Finset.mem_biUnion.mpr ⟨edge i,Finset.mem_map.mpr ⟨i,hi,rfl⟩,by simp [shape]⟩
theorem star_floor {m n k} (C : Circuit) (mono : Monotone2 C)
    (ends : Fin n → Finset (Fin m)) (f : Pins m → Bool) (u : Pins m) (ok : Match C f u)
    (rep : ∀ s, f (covered ends s)=true ↔ 2≤s.card)
    (center : Fin m) (neighbor : Fin k ↪ Fin m) (edge : Fin k ↪ Fin n)
    (shape : ∀ i,ends (edge i)={center,neighbor i})
    (center_kept : center∈u) (kept : ∀ i,neighbor i∈u) (pos : 0<k) :
    2*k-4 ≤ ors C.gates := by
  classical
  let E := circuit C (assignment center neighbor)
  obtain ⟨em,price,sim⟩ := reindex C mono (assignment center neighbor)
  have nonempty (s : Finset (Fin k)) (hs : s.Nonempty) :
      E.eval (vector s)=true ↔ 2≤s.card := by
    have sub : insert center (s.map neighbor) ⊆ u := by
      intro z hz
      rcases Finset.mem_insert.mp hz with rfl|hz
      · exact center_kept
      · obtain ⟨i,_,rfl⟩ := Finset.mem_map.mp hz
        exact kept i
    rw [show E.eval (vector s)=_ from sim _ (by simp [vector]),assigned_row,ok _ sub,
      ←covered_star center neighbor edge ends shape s hs]
    simpa using rep (s.map edge)
  have full : Computes k E := by
    intro s
    by_cases hs : s.Nonempty
    · exact nonempty s hs
    · have emp := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      let i : Fin k := ⟨0,pos⟩
      constructor
      · intro on
        have hxy : ExtendsBits (vector (∅ : Finset (Fin k))) (vector {i}) := by
          refine ⟨by simp [vector],?_⟩
          intro j h
          rw [vec_get] at h
          split at h <;> simp at h
        have two := (nonempty {i} (by simp)).mp (circuit_mono E em _ _ hxy on)
        simp at two
      · simp
  have base := FreeAndNet.threshold_two_circuit_or_lower k E em full
  have counts : (E.gates.filter FreeAndNet.CircuitCompiler.orFlag).length=ors E.gates := by
    have flags : FreeAndNet.CircuitCompiler.orFlag=isOr := by funext g; cases g with | mk op ins => cases op <;> rfl
    rw [flags,ors,List.countP_eq_length_filter]
  exact (base.trans_eq counts).trans price

#print axioms star_floor
end ThresholdStarTruth
