import DDRootCount
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {orig : Circuit} (F : RootForest G orig)
theorem branch_for_pair (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (closed : F.Closed) (apart : ∀ r∈F.roots, ∀ t∈F.roots, ¬ F.Up r t)
    {g : ℕ} (valid : g<F.net.size) (hand : (gateAt F.net g).op = .and)
    (two : 2 ≤ (F.ends g).card) :
    ∃ j, Relation.ReflTransGen F.step g j ∧ F.Product j ∧ 2 ≤ (F.liveReaders j).card ∧ F.ends j = F.ends g := by
  classical
  obtain ⟨r,hr,t,ht,ne⟩ := Finset.one_lt_card.mp two
  obtain ⟨rr,gr⟩ := F.mem_ends.mp hr
  obtain ⟨rt,gt⟩ := F.mem_ends.mp ht
  have excl {v w : ℕ} (vv : v∈F.roots) (ww : w∈F.roots) (vw : v≠w)
      (p : Relation.ReflTransGen F.trim v w) : False := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp (F.forget_trim p) with eq|q
    · exact vw eq.symm
    · exact apart v vv w ww (F.from_path q)
  obtain ⟨j,gj,fork,jr,jt⟩ := Incidence.fork_of_incomparable F.trim
    (F.trim_path (F.to_path gr).to_reflTransGen ⟨r,rr,.inl rfl⟩)
    (F.trim_path (F.to_path gt).to_reflTransGen ⟨t,rt,.inl rfl⟩)
    (excl rr rt ne) (excl rt rr (fun h => ne h.symm))
  have path := F.forget_trim gj
  have real {u v} (p : Relation.TransGen F.trim u v) : F.Up u v := by
    apply F.from_path
    induction p with
    | single h => exact .single h.1
    | tail _ h ih => exact ih.tail h.1
  have jv : j<F.net.size ∧ (gateAt F.net j).op = .and := by
    rcases Relation.reflTransGen_iff_eq_or_transGen.mp path with eq|h
    · simpa [eq] using And.intro valid hand
    · have p := F.from_path h
      obtain ⟨i,hi,eq,_⟩ := p
      have ji : j=i := by omega
      exact ⟨by simpa [ji] using hi,(F.descendants closed hand (F.from_path h)).1⟩
  have low : 2≤(F.ends j).card := Finset.one_lt_card.mpr
    ⟨r,F.mem_ends.mpr ⟨rr,real jr⟩,t,F.mem_ends.mpr ⟨rt,real jt⟩,ne⟩
  have sub : F.ends j ⊆ F.ends g := by
    intro v hv
    obtain ⟨rv,jp⟩ := F.mem_ends.mp hv
    exact F.mem_ends.mpr ⟨rv,F.from_path (Relation.TransGen.trans_right path (F.to_path jp))⟩
  have bound := F.all_root_count least edge closed apart valid hand
  exact ⟨j,path,F.product_of_fork least edge closed jv.1 jv.2 fork,F.fork_count fork,
    Finset.eq_of_subset_of_card_le sub (by omega)⟩

theorem pairwise_intersection (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (closed : F.Closed) (apart : ∀ r∈F.roots, ∀ t∈F.roots, ¬ F.Up r t)
    {a b : ℕ} (av : a<F.net.size) (ah : (gateAt F.net a).op = .and) (aa : 2 ≤ (F.ends a).card)
    (bv : b<F.net.size) (bh : (gateAt F.net b).op = .and) (bb : 2 ≤ (F.ends b).card) :
    ((F.ends a) ∩ (F.ends b)).Nonempty := by
  obtain ⟨u,_,pu,cu,hu⟩ := F.branch_for_pair least edge closed apart av ah aa
  obtain ⟨v,_,pv,cv,hv⟩ := F.branch_for_pair least edge closed apart bv bh bb
  rw [←hu,←hv]
  exact F.intersects least edge pu pv cu cv
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
