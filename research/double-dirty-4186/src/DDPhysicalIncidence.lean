import DDRootForest
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
namespace RootForest
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {orig : Circuit} (F : RootForest G orig)
theorem antichain {a b : ℕ} (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (pa : F.Product a) (pb : F.Product b) (aa : 2≤(F.liveReaders a).card)
    (bb : 2≤(F.liveReaders b).card) : ¬ F.Up a b := by
  classical
  intro ab
  have ne : a ≠ b := by have := source_lt_of_strict F.ao ab; omega
  by_cases dis : Disjoint (F.liveReaders a) (F.liveReaders b)
  · have bound := F.laminar_cap least edge pb pa true
      (fun _ _ path => ⟨fun _ => rfl, fun _ => strict_trans ab path⟩)
    have low := F.four_readers bb aa dis.symm
    omega
  obtain ⟨z,hz⟩ := Finset.not_disjoint_iff_nonempty_inter.mp dis
  obtain ⟨za,zb⟩ := Finset.mem_inter.mp hz
  obtain ⟨u,hu,v,hv,uv⟩ := Finset.one_lt_card.mp bb
  obtain ⟨v,hv,zv⟩ : ∃ v ∈ F.liveReaders b, z ≠ v := by
    by_cases zu : z=u
    · exact ⟨v,hv,fun h => uv (zu.symm.trans h)⟩
    · exact ⟨u,hu,zu⟩
  have zl := F.mem_live.mp zb
  have vl := F.mem_live.mp hv
  obtain ⟨r,hr⟩ := F.reached zb
  have aliveB : F.Alive b := ⟨r,(F.mem_ends.mp hr).1,.inr (F.mem_ends.mp hr).2⟩
  apply no_comparable_common F.net F.ao ne zv (F.mem_live.mp za).1 zl.1 vl.1
    (pb.downstream z (reader_reach zl.1) zl.2).1 (pb.downstream v (reader_reach vl.1) vl.2).1
    (pa.downstream b ab aliveB).2
  · exact reader_of_live_alias pb.dirty F.root_clean zl.2
  · exact reader_of_live_alias pb.dirty F.root_clean vl.2
  · intro S inc aliases
    apply cap_alias_group G orig F.net least F.ao F.roots F.valid F.cover F.near b pb.valid pb.dirty
      ⟨r,(F.mem_ends.mp hr).1,(F.mem_ends.mp hr).2⟩
      (fun t ht path => (pb.downstream t path ⟨t,ht,.inl rfl⟩).2) S inc _ aliases
    intro i hi
    by_cases same : i=b
    · simpa [same] using pb.valid
    · obtain ⟨j,len,eq,_⟩ := (aliases i hi same).1
      have eq' : i=j := by omega
      simpa [eq'] using len

theorem intersects {a b : ℕ} (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (pa : F.Product a) (pb : F.Product b) (aa : 2≤(F.liveReaders a).card)
    (bb : 2≤(F.liveReaders b).card) : ((F.ends a) ∩ (F.ends b)).Nonempty := by
  classical
  by_contra empty
  have no (t) (ha : t∈F.ends a) (hb : t∈F.ends b) := empty ⟨t,Finset.mem_inter.mpr ⟨ha,hb⟩⟩
  have bound := F.laminar_cap least edge pa pb false (by
    intro t ht p
    exact ⟨fun q => (no t (F.mem_ends.mpr ⟨ht,p⟩) (F.mem_ends.mpr ⟨ht,q⟩)).elim, by simp⟩)
  have dis : Disjoint (F.liveReaders a) (F.liveReaders b) := by
    apply Finset.disjoint_left.mpr
    intro j ja jb
    obtain ⟨ra,t,ht,eq|endj⟩ := F.mem_live.mp ja
    · subst j
      exact no t (F.mem_ends.mpr ⟨ht,reader_reach ra⟩)
        (F.mem_ends.mpr ⟨ht,reader_reach (F.mem_live.mp jb).1⟩)
    · exact no t (F.mem_ends.mpr ⟨ht,strict_trans (reader_reach ra) endj⟩)
        (F.mem_ends.mpr ⟨ht,strict_trans (reader_reach (F.mem_live.mp jb).1) endj⟩)
  have low := F.four_readers aa bb dis
  omega

end RootForest
end PEqualNP.Outside.L_meta_4186_aux.Q1Double
