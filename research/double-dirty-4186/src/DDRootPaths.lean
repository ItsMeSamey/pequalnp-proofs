import DDIndexedDominance
import DDPhysicalIncidence
import DDCleanCap
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {orig : Circuit} (F : RootForest G orig)
def step (a j : ℕ) := j ∈ readers n F.net a
def trim (a j : ℕ) := F.step a j ∧ F.Alive j
theorem influence_path {a w : ℕ} (p : Influence n F.net a w) :
    ∃ j, w=n+j ∧ Relation.ReflTransGen F.step a j := by
  induction p with
  | source => exact ⟨_,rfl,.refl⟩
  | step _ bound pin ih =>
    obtain ⟨j,rfl,path⟩ := ih
    exact ⟨_,rfl,path.tail (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr bound,pin⟩)⟩
theorem to_path {a j : ℕ} (p : F.Up a j) : Relation.TransGen F.step a j := by
  obtain ⟨k,hk,eq,u,hu,prev⟩ := p
  have jk : j=k := by omega
  subst k
  obtain ⟨z,rfl,rt⟩ := F.influence_path prev
  exact Relation.TransGen.tail' rt (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hk,hu⟩)
theorem from_path {a j : ℕ} (p : Relation.TransGen F.step a j) : F.Up a j := by
  induction p with
  | single h => exact reader_reach h
  | tail _ h ih => exact strict_trans ih (reader_reach h)

theorem back_alive {a j : ℕ} (aj : Relation.ReflTransGen F.step a j) (hj : F.Alive j) : F.Alive a := by
  obtain ⟨t,ht,eq|path⟩ := hj
  · subst j
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp aj with eq|p
    · exact ⟨t,ht,.inl eq.symm⟩
    · exact ⟨t,ht,.inr (F.from_path p)⟩
  · exact ⟨t,ht,.inr (F.from_path (Relation.TransGen.trans_right aj (F.to_path path)))⟩

theorem trim_path {a j : ℕ} (aj : Relation.ReflTransGen F.step a j) (alive : F.Alive j) :
    Relation.ReflTransGen F.trim a j := by
  induction aj using Relation.ReflTransGen.head_induction_on with
  | refl => exact .refl
  | head e p ih => exact .head ⟨e,F.back_alive p alive⟩ ih

theorem forget_trim {a j : ℕ} (p : Relation.ReflTransGen F.trim a j) :
    Relation.ReflTransGen F.step a j := by
  induction p with
  | refl => exact .refl
  | tail _ h ih => exact ih.tail h.1

theorem fork_count {g : ℕ} (h : Incidence.Fork F.trim g) : 2 ≤ (F.liveReaders g).card := by
  obtain ⟨a,b,ha,hb,ne⟩ := h
  exact Finset.one_lt_card.mpr ⟨a,F.mem_live.mpr ha,b,F.mem_live.mpr hb,ne⟩

def Closed := ∀ {i j}, (gateAt F.net i).op = .and → j<F.net.size →
  n+i ∈ (gateAt F.net j).inputs → (gateAt F.net j).op = .and

theorem descendants {s t : ℕ} (closed : F.Closed) (hand : (gateAt F.net s).op = .and)
    (path : F.Up s t) : (gateAt F.net t).op = .and ∧
    ∀ x, gateVal n F.net t x = true → gateVal n F.net s x = true := by
  obtain ⟨j,eq,aj,dom⟩ := Indexed.dominated_path F.net F.ao closed hand (strict_to_influence path)
  have q : t=j := by omega
  subst j
  exact ⟨aj,dom⟩
theorem product_of_fork {g : ℕ} (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (closed : F.Closed) (valid : g<F.net.size) (hand : (gateAt F.net g).op = .and)
    (fork : Incidence.Fork F.trim g) : F.Product g := by
  classical
  have count := F.fork_count fork
  obtain ⟨u,hu,_,_,_⟩ := Finset.one_lt_card.mp count
  have live := F.reached hu
  refine ⟨valid,?_,fun _ path _ => F.descendants closed hand path⟩
  intro clean
  have cap := clean_cap_one G orig F.net least F.ao F.roots F.valid F.cover edge F.near g valid
    (F.ends g) (Finset.filter_subset _ _) live clean (by
      rintro x ⟨t,ht,on⟩
      exact (F.descendants closed hand (F.mem_ends.mp ht).2).2 x on)
    (by intro t ht path; exact (Finset.mem_sdiff.mp ht).2
          (F.mem_ends.mpr ⟨(Finset.mem_sdiff.mp ht).1,path⟩))
  have size := Finset.card_le_card (Finset.filter_subset (F.Alive) (readers n F.net g))
  change (F.liveReaders g).card ≤ (readers n F.net g).card at size
  omega

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
