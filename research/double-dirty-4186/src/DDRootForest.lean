import DDSharedQuota
import DDComparable
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
structure RootForest {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (orig : Circuit) where
  net : Circuit
  ao : IsAO2 n net
  roots : Finset ℕ
  valid : ∀ t ∈ roots, t < net.size
  cover : ∀ x, graphFun G ∅ x = true ↔ ∃ t ∈ roots, gateVal n net t x = true
  near : net.size + roots.card ≤ orig.size + 2
namespace RootForest
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {orig : Circuit} (F : RootForest G orig)
def Up (g j : ℕ) := strictInfluence n F.net g (n+j)
def Alive (j : ℕ) := ∃ t ∈ F.roots, j=t ∨ F.Up j t
noncomputable def liveReaders (g : ℕ) : Finset ℕ := by
  classical
  exact (readers n F.net g).filter (F.Alive)
noncomputable def ends (g : ℕ) : Finset ℕ := by
  classical
  exact F.roots.filter (F.Up g)
theorem mem_ends {g t : ℕ} : t ∈ F.ends g ↔ t ∈ F.roots ∧ F.Up g t := by
  classical
  exact Finset.mem_filter
theorem mem_live {g j : ℕ} : j ∈ F.liveReaders g ↔ j ∈ readers n F.net g ∧ F.Alive j := by
  classical
  exact Finset.mem_filter
structure Product (g : ℕ) : Prop where
  valid : g < F.net.size
  dirty : ¬ BelowF G F.net g
  downstream : ∀ j, F.Up g j → F.Alive j → (gateAt F.net j).op = .and ∧
    ∀ x, gateVal n F.net j x = true → gateVal n F.net g x = true
theorem root_clean (t : ℕ) (ht : t∈F.roots) : BelowF G F.net t :=
  fun x h => (F.cover x).mpr ⟨t,ht,h⟩
theorem reached {g v : ℕ} (hv : v ∈ F.liveReaders g) : (F.ends g).Nonempty := by
  obtain ⟨rd,t,ht,eq|path⟩ := F.mem_live.mp hv
  · subst v
    exact ⟨t,F.mem_ends.mpr ⟨ht,reader_reach rd⟩⟩
  · exact ⟨t,F.mem_ends.mpr ⟨ht,strict_trans (reader_reach rd) path⟩⟩
theorem cap {g : ℕ} (least : IsLeastAO G orig) (pg : F.Product g) (live : (F.ends g).Nonempty) :
    (readers n F.net g).card ≤ 2 := by
  obtain ⟨r,hr⟩ := live
  apply cap_two G orig F.net least F.ao F.roots F.valid F.cover F.near g pg.valid pg.dirty
    ⟨r,(F.mem_ends.mp hr).1,(F.mem_ends.mp hr).2⟩
  intro t ht path
  exact (pg.downstream t path ⟨t,ht,.inl rfl⟩).2
theorem four_readers {a b : ℕ} (aa : 2≤(F.liveReaders a).card) (bb : 2≤(F.liveReaders b).card)
    (dis : Disjoint (F.liveReaders a) (F.liveReaders b)) :
    4≤((readers n F.net a) ∪ (readers n F.net b)).card := by
  classical
  have sub : F.liveReaders a ∪ F.liveReaders b ⊆ readers n F.net a ∪ readers n F.net b :=
    Finset.union_subset_union (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h := Finset.card_le_card sub
  rw [Finset.card_union_of_disjoint dis] at h
  omega
theorem laminar_cap {a b : ℕ} (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (pa : F.Product a) (pb : F.Product b) (nested : Bool)
    (shape : ∀ t∈F.roots, F.Up a t → (F.Up b t ↔ nested = true)) :
    ((readers n F.net a) ∪ (readers n F.net b)).card ≤ 3 := by
  have star := laminar_reader_union G orig F.net least F.ao F.roots F.valid F.cover edge F.near
    a b {a,b} (by simp) (by simp) (by simp [pa.valid,pb.valid]) (by simp) nested shape (by
      intro t ht s eq path
      rcases eq with rfl|rfl
      · exact (pa.downstream t path ⟨t,ht,.inl rfl⟩).2
      · exact (pb.downstream t path ⟨t,ht,.inl rfl⟩).2)
  simpa using star
end RootForest
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
