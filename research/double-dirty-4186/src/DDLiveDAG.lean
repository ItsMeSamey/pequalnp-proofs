import DDVirtualDAG
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual.DAG
def Live (D : DAG) (v : Node) : Prop :=
  ∃ r ∈ D.roots, Relation.ReflTransGen D.step v r.node
def liveStep (D : DAG) (u v : Node) := D.step u v ∧ Live D v
noncomputable def liveReaders (D : DAG) (g : ℕ) : Finset Node := by
  classical
  exact (D.readers g).filter (Live D)
theorem mem_liveReaders {D : DAG} {g v} :
    v ∈ D.liveReaders g ↔ v ∈ D.readers g ∧ Live D v := by
  classical
  exact Finset.mem_filter

theorem endpoint_live {D : DAG} {u v : Node} (path : Relation.ReflTransGen D.step u v)
    (h : Live D v) : Live D u := by
  obtain ⟨r,hr,p⟩ := h
  exact ⟨r,hr,path.trans p⟩

theorem trim_path {D : DAG} {u v : Node} (path : Relation.ReflTransGen D.step u v)
    (h : Live D v) : Relation.ReflTransGen D.liveStep u v := by
  induction path using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head e p ih => exact .head ⟨e,endpoint_live p h⟩ ih

theorem has_next {D : DAG} {v : Node} (h : Live D v)
    (internal : ∀ r ∈ D.roots, v ≠ r.node) : ∃ w, D.liveStep v w := by
  obtain ⟨r,hr,p⟩ := h
  rcases Relation.ReflTransGen.cases_head p with eq | ⟨w,step,tail⟩
  · exact (internal r hr eq).elim
  · exact ⟨w, step, r, hr, tail⟩

theorem live_fork_iff {D : DAG} {g : ℕ} (present : g ∈ D.paidRows) (internal : g ∉ D.extTops) :
    Incidence.Fork D.liveStep (.row g) ↔ 2 ≤ (D.liveReaders g).card := by
  constructor
  · rintro ⟨a,b,ha,hb,ne⟩
    exact Finset.one_lt_card.mpr ⟨a,mem_liveReaders.mpr ⟨ha.1.2.2,ha.2⟩,
      b,mem_liveReaders.mpr ⟨hb.1.2.2,hb.2⟩,ne⟩
  · intro count
    obtain ⟨a,ha,b,hb,ne⟩ := Finset.one_lt_card.mp count
    obtain ⟨ra,la⟩ := mem_liveReaders.mp ha
    obtain ⟨rb,lb⟩ := mem_liveReaders.mp hb
    exact ⟨a,b,⟨⟨present,internal,ra⟩,la⟩,⟨⟨present,internal,rb⟩,lb⟩,ne⟩
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual.DAG
