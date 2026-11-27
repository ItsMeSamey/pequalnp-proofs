import DDMixerGuard
import Q1DoubleSplitActual
import Q0Aggregation
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.CleanedNonEdge
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

private theorem splitArm {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) (b : Fin 2) :
    ∃ i ∈ junk G C, opnd C m b = n+i ∧ splitSlot G C m (n+i) = some (gateVal n C i) := by
  obtain ⟨i,hi,eq⟩ := d.pins b
  refine ⟨i,hi,eq,?_⟩
  obtain ⟨il,io,_⟩ := (S4183.junk_iff G C i).mp hi
  have pin := opnd_mem least.1 (mixer_info d).1 b
  have bound := least.1.2.1 m (mixer_info d).1 _ pin
  rw [eq] at bound
  have unaffected : ¬ Influence n C m (n+i) := fun path => by have := influence_le least.1 path; omega
  have keep : Kept G C (n+i) := by
    intro j hj e
    have same : j=i := by omega
    subst j
    exact GateOp.noConfusion (io.symm.trans (Finset.mem_filter.mp hj).2.1)
  have width : n+i < n+C.size := Nat.add_lt_add_left il n
  have old (x : Fin n → Bool) : gateVal n C i x = denotation (splitSlot G C m (n+i)) x :=
    root_cofactor G C m edge least form true width keep x (fun path => (unaffected path).elim)
  cases h : splitSlot G C m (n+i) with
  | none =>
    have hz := old (fun _ => false)
    have zero := zero_wire C least.1 _ width
    change gateVal n C i (fun _ => false) = false at zero
    simp [h,zero,denotation] at hz
  | some f =>
    have eqf : gateVal n C i=f := funext fun x => by simpa [h,denotation] using old x
    rw [eqf]

private theorem list_or_iff {n : ℕ} (fs : List (Signal n)) (hd : Signal n) (x : Fin n → Bool) :
    fs.foldl (join false) hd x = true ↔ hd x = true ∨ ∃ f ∈ fs, f x = true := by
  induction fs generalizing hd with
  | nil => simp
  | cons f fs ih =>
    rw [List.foldl_cons,ih]
    simp only [join,Bool.false_eq_true,if_false,Bool.or_eq_true_iff,List.mem_cons]
    aesop

structure SplitData {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (m : ℕ) where
  a : ℕ
  b : ℕ
  t : ℕ
  w : Signal n
  other : List (Signal n)
  aJunk : a ∈ junk G C
  bJunk : b ∈ junk G C
  top : t ∈ tops G C
  affected : Influence n C m (n+t)
  onlyAffected : ∀ i∈tops G C, Influence n C m (n+i) → i=t
  other_eq : other = ((tops G C).erase t).toList.map (gateVal n C)
  left : opnd C m 0 = n+a
  right : opnd C m 1 = n+b
  leftSlot : splitSlot G C m (n+a) = some (gateVal n C a)
  rightSlot : splitSlot G C m (n+b) = some (gateVal n C b)
  guardSlot : splitSlot G C m (n+t) = some w
  retained : ∀ f∈other, ∃ i, i∈tops G C ∧ splitSlot G C m (n+i) = some f
  count : other.length ≤ (orT G C).card
  agree : other.foldl (join false) (join true (join false (gateVal n C a) (gateVal n C b)) w) = circuitFun n C

theorem split_data {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) : Nonempty (SplitData G C m) := by
  classical
  obtain ⟨a,ha,pa,slotA⟩ := splitArm G C m d edge least form 0
  obtain ⟨b,hb,pb,slotB⟩ := splitArm G C m d edge least form 1
  obtain ⟨t,⟨ht,path⟩,uniq⟩ := unique_influenced_top d edge least form
  obtain ⟨w,slotW,guard⟩ := split_guard_real d edge least form ht path
  let els := ((tops G C).erase t).toList
  let others := els.map (gateVal n C)
  have mem (j : ℕ) : j ∈ els ↔ j≠t ∧ j∈tops G C := by simp [els,Finset.mem_erase]
  have stable (j : ℕ) (hj : j∈els) : splitSlot G C m (n+j) = some (gateVal n C j) := by
    obtain ⟨ne,top⟩ := (mem j).mp hj
    exact unchanged_top_slot d edge least form top (fun influence => ne (uniq j ⟨top,influence⟩))
  have count := Q0.clean_or_count G C edge least form
  have card : others.length ≤ (orT G C).card := by
    simp only [others,els,List.length_map,Finset.length_toList,Finset.card_erase_of_mem ht]
    omega
  have mix (x : Fin n → Bool) : gateVal n C m x = (gateVal n C a x || gateVal n C b x) := by
    obtain ⟨real,op,_⟩ := mixer_info d
    obtain ⟨_,u,v,ps,hu,hv⟩ := AO_of_IsAO2 n C least.1 m real
    have ea : u=n+a := by simpa [opnd,ps] using pa
    have eb : v=n+b := by simpa [opnd,ps] using pb
    subst u
    subst v
    exact W_or n C x m real op _ _ ps hu hv
  have sem : others.foldl (join false) (join true (join false (gateVal n C a) (gateVal n C b)) w)
      = circuitFun n C := by
    funext x
    apply Bool.eq_iff_iff.mpr
    rw [list_or_iff,least.2.1,Q0.graph_iff_top G C edge least]
    have h : (join true (join false (gateVal n C a) (gateVal n C b)) w x) = gateVal n C t x := by
      simpa [join,mix x] using (guard x).symm
    rw [h]
    constructor
    · rintro (yes|⟨f,hf,yes⟩)
      · exact ⟨t,ht,yes⟩
      · obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
        exact ⟨j,((mem j).mp hj).2,yes⟩
    · rintro ⟨j,hj,yes⟩
      by_cases eq : j=t
      · subst j; exact Or.inl yes
      · exact Or.inr ⟨gateVal n C j,List.mem_map.mpr ⟨j,(mem j).mpr ⟨eq,hj⟩,rfl⟩,yes⟩
  refine ⟨⟨a,b,t,w,others,ha,hb,ht,path,(fun i hi inf => uniq i ⟨hi,inf⟩),rfl,pa,pb,slotA,slotB,slotW,?_,card,sem⟩⟩
  intro f hf
  obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hf
  exact ⟨j,((mem j).mp hj).2,stable j hj⟩

theorem graph_split {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit)
    (m : ℕ) (d : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C)
    (form : PEqualNP.TopForm.TopForm G C) :
    let k := expense (seed n) (rows n C (splitCuts n C (orT G C) m) C.size)
    ∃ a ∈ junk G C, ∃ b ∈ junk G C, ∃ w : Signal n, ∃ D : Circuit,
      opnd C m 0 = n+a ∧ opnd C m 1 = n+b ∧ IsAO2 n D ∧ D.size ≤ C.size+1 ∧
      wireVal n D (n+k) = join true (gateVal n C a) w ∧
      wireVal n D (n+(k+1)) = join true (gateVal n C b) w ∧ circuitFun n D = circuitFun n C := by
  classical
  dsimp only
  obtain ⟨z⟩ := split_data G C m d edge least form
  obtain ⟨B,tr,slots⟩ := compiled_rows n C (splitCuts n C (orT G C) m) C.size
  have haveSlot {v f} (h : splitSlot G C m v = some f) : B f := by
    have hh := slots v
    change physically B (splitSlot G C m v) at hh
    simpa only [h,physically] using hh
  have ho (f) (hf : f∈z.other) : B f := by
    obtain ⟨j,_,h⟩ := z.retained f hf
    exact haveSlot h
  have budget := mixer_split_budget d edge least
  have count := z.count
  obtain ⟨D,hD,sz,aw,bw,same⟩ := split_competitor tr C _ _ _ z.other
    (haveSlot z.leftSlot) (haveSlot z.rightSlot) (haveSlot z.guardSlot) ho (by omega) z.agree
  exact ⟨z.a,z.aJunk,z.b,z.bJunk,z.w,D,z.left,z.right,hD,sz,aw,bw,same⟩

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
