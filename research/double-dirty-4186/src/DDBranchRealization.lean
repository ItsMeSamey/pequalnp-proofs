import DDBranchLift
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Indexed Q0.Factor
attribute [local instance] gateOpDecEq

theorem fork_reaching_arm_external {V : DAG} {g t : ℕ} {b : Fin 2}
    (ext : t ∈ V.extTops)
    (a : Relation.ReflTransGen V.step (.row g) (.arm b))
    (e : Relation.ReflTransGen V.step (.row g) (.row t)) :
    ∃ f ∈ V.paidRows, Relation.ReflTransGen V.liveStep (.row g) (.row f) ∧
      Incidence.Fork V.liveStep (.row f) ∧ Root.arm b ∈ V.reaches f ∧ Root.ext t ∈ V.reaches f := by
  have ha : Root.arm b ∈ V.roots := by simp [DAG.roots]
  have he : Root.ext t ∈ V.roots := by simp [DAG.roots,ext]
  have stop {r : Root} (hr : r ∈ V.roots) {v : Node}
      (p : Relation.ReflTransGen V.liveStep r.node v) : r.node = v := by
    rcases Relation.ReflTransGen.cases_head p with eq | ⟨s,hs,_⟩
    · exact eq
    · exact (V.terminal hr s hs.1).elim
  have ar := DAG.trim_path a (show V.Live (.arm b) from ⟨.arm b,ha,.refl⟩)
  have er := DAG.trim_path e (show V.Live (.row t) from ⟨.ext t,he,.refl⟩)
  obtain ⟨f,reach,fork,fa,fe⟩ := Incidence.fork_of_incomparable V.liveStep ar er
    (fun p => Node.noConfusion (stop ha p)) (fun p => Node.noConfusion (stop he p))
  have forget {u v : Node} (p : Relation.TransGen V.liveStep u v) : Relation.ReflTransGen V.step u v := by
    induction p with
    | single h => exact .single h.1
    | tail _ h ih => exact ih.tail h.1
  obtain ⟨s,v,hs,hv,ne⟩ := fork
  cases f with
  | arm k => exact False.elim hs.1
  | row f =>
    exact ⟨f,hs.1.1,reach,⟨s,v,hs,hv,ne⟩,DAG.mem_reaches.mpr ⟨ha,forget fa⟩,
      DAG.mem_reaches.mpr ⟨he,forget fe⟩⟩

theorem realized_indexed_label {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj]
    {C : Circuit} {m a t j : ℕ} (D : DoubleDirty G C m) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) (E : Finset ℕ)
    (external : E ⊆ tops G C) (A : Fin 2 → ℕ) (W : ℕ) (b : Fin 2)
    (arm : opnd C m b = n+a) (address : A b = n+a)
    (ext : t ∈ E) (off : ¬ Influence n C m (n+t))
    (ja : j ∈ andRegion n C a) (jt : j ∈ andRegion n C t) :
    let V := indexed n C (splitCuts n C (orT G C) m) E A W
    ∃ f ∈ V.paidRows, Relation.ReflTransGen V.liveStep (.row j) (.row f) ∧
      Incidence.Fork V.liveStep (.row f) ∧ Root.arm b ∈ V.reaches f ∧ Root.ext t ∈ V.reaches f := by
  let p := splitCuts n C (orT G C) m
  let V := indexed n C p E A W
  obtain ⟨a',dirty,eq⟩ := D.pins b
  have same : a'=a := by omega
  subst a'
  obtain ⟨ab,op,_⟩ := (S4183.junk_iff G C a).mp dirty
  have pin := opnd_mem least.1 (mixer_info D).1 b
  have back := least.1.2.1 m (mixer_info D).1 _ pin
  have offa : ¬ Influence n C m (n+a) := fun h => by have := influence_le least.1 h; omega
  have noExt {i} (h : i ∈ junk G C) : i ∉ E := fun ie =>
    ((S4183.junk_iff G C i).mp h).2.2 (Finset.mem_filter.mp (external ie)).2.2
  have pa := region_indexed_path edge least form E A W offa ja
    (fun i hi _ => noExt (dirty_region_sub least.1 form dirty hi))
  obtain ⟨g,paid⟩ := unaffected_and_paid edge least form ab op offa
  have real : a ∈ V.paidRows := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ab,by simp [p,paid],op⟩
  have ar : Node.arm b ∈ V.readers a := by
    apply (indexed_reads_arm C p E A W b).mpr
    refine ⟨0,?_⟩
    simp [address,producer,paid_ref C p paid ab]
  obtain ⟨ht,ot,_⟩ := Finset.mem_filter.mp (external ext)
  have et := region_indexed_path edge least form E A W off jt
    (fun i hi ne => noExt (region_except_root_dirty least.1 form (Finset.mem_range.mp ht) ot
      (Finset.mem_erase.mpr ⟨ne,hi⟩)))
  exact fork_reaching_arm_external (V:=V) ext (pa.tail ⟨real,noExt dirty,ar⟩) et

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
