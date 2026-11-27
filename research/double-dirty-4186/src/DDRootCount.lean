import DDRootPaths
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm PEqualNP.EdgeOwnership PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] gateOpDecEq
variable {n : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {orig : Circuit} (F : RootForest G orig)
theorem root_count {g : ℕ} (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (closed : F.Closed) (valid : g<F.net.size) (hand : (gateAt F.net g).op = .and)
    (branch : Incidence.Fork F.trim g)
    (rootsApart : ∀ r∈F.roots, ∀ t∈F.roots, ¬ F.Up r t) : (F.ends g).card ≤ 2 := by
  classical
  have prod := F.product_of_fork least edge closed valid hand branch
  obtain ⟨u,hu,_,_,_⟩ := Finset.one_lt_card.mp (F.fork_count branch)
  have cap := F.cap least prod (F.reached hu)
  have split (r) (hr : r∈F.ends g) : ∃ v∈readers n F.net g,
      F.trim g v ∧ Relation.ReflTransGen F.trim v r := by
    obtain ⟨rt,path⟩ := F.mem_ends.mp hr
    obtain ⟨v,gv,vr⟩ := Relation.TransGen.head'_iff.mp (F.to_path path)
    have live : F.Alive r := ⟨r,rt,.inl rfl⟩
    exact ⟨v,gv,⟨gv,F.back_alive vr live⟩,F.trim_path vr live⟩
  let reader (r : ↥(F.ends g)) : ↥(readers n F.net g) :=
    ⟨(split r.val r.property).choose,(split r.val r.property).choose_spec.1⟩
  have inj : Function.Injective reader := by
    intro r s eq
    have h := congrArg Subtype.val eq
    change (split r.val r.property).choose = (split s.val s.property).choose at h
    have pr := (split r.val r.property).choose_spec.2
    have ps := (split s.val s.property).choose_spec.2
    rw [←h] at ps
    apply Subtype.ext
    by_contra ne
    have exclude {v w : ℕ} (vv : v∈F.roots) (ww : w∈F.roots) (different : v ≠ w)
        (p : Relation.ReflTransGen F.trim v w) : False := by
      rcases Relation.reflTransGen_iff_eq_or_transGen.mp (F.forget_trim p) with e|q
      · exact different e.symm
      · exact rootsApart v vv w ww (F.from_path q)
    have rr := (F.mem_ends.mp r.property).1
    have sr := (F.mem_ends.mp s.property).1
    obtain ⟨j,vj,bj,_,_⟩ := Incidence.fork_of_incomparable F.trim pr.2 ps.2
      (exclude rr sr ne) (exclude sr rr (fun h => ne h.symm))
    have pgj : F.Up g j := F.from_path (Relation.TransGen.head' pr.1.1 (F.forget_trim vj))
    obtain ⟨jj,jlen,jeq,_⟩ := pgj
    have idj : j=jj := by omega
    have pgj := F.from_path (Relation.TransGen.head' pr.1.1 (F.forget_trim vj))
    have pj := F.product_of_fork least edge closed (by simpa [idj] using jlen)
      (F.descendants closed hand pgj).1 bj
    exact F.antichain least edge prod pj (F.fork_count branch) (F.fork_count bj) pgj
  have bound : (F.ends g).card ≤ (readers n F.net g).card := by
    simpa using Fintype.card_le_of_injective reader inj
  exact bound.trans cap

theorem all_root_count (least : IsLeastAO G orig) (edge : G.edgeFinset.Nonempty)
    (closed : F.Closed) (rootsApart : ∀ r∈F.roots, ∀ t∈F.roots, ¬ F.Up r t)
    {g : ℕ} (valid : g<F.net.size) (hand : (gateAt F.net g).op = .and) :
    (F.ends g).card ≤ 2 := by
  classical
  have all (k : ℕ) : ∀ j, F.net.size-j=k → j<F.net.size →
      (gateAt F.net j).op = .and → (F.ends j).card ≤ 2 := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro j key len op
      by_cases fork : Incidence.Fork F.trim j
      · exact F.root_count least edge closed len op fork rootsApart
      by_cases any : (F.ends j).Nonempty
      · obtain ⟨r,hr⟩ := any
        have first {t} (ht : t∈F.ends j) : ∃ v∈F.liveReaders j,
            v=t ∨ F.Up v t := by
          obtain ⟨rt,path⟩ := F.mem_ends.mp ht
          obtain ⟨v,step,tail⟩ := Relation.TransGen.head'_iff.mp (F.to_path path)
          rcases Relation.reflTransGen_iff_eq_or_transGen.mp tail with eq|p
          · subst v
            exact ⟨t,F.mem_live.mpr ⟨step,t,rt,.inl rfl⟩,.inl rfl⟩
          · have h := F.from_path p
            exact ⟨v,F.mem_live.mpr ⟨step,t,rt,.inr h⟩,.inr h⟩
        obtain ⟨v,hv,_⟩ := first hr
        have uniq {w} (hw : w∈F.liveReaders j) : v=w := by
          by_contra neq
          exact fork ⟨v,w,F.mem_live.mp hv,F.mem_live.mp hw,neq⟩
        have via {t} (ht : t∈F.ends j) : v=t ∨ F.Up v t := by
          obtain ⟨w,hw,p⟩ := first ht
          simpa only [uniq hw] using p
        by_cases vr : v∈F.roots
        · have sub : F.ends j ⊆ {v} := by
            intro t ht
            rcases via ht with eq|p
            · exact Finset.mem_singleton.mpr eq.symm
            · exact (rootsApart v vr t (F.mem_ends.mp ht).1 p).elim
          exact (Finset.card_le_card sub).trans (by simp)
        · have sub : F.ends j ⊆ F.ends v := by
            intro t ht
            have htt := (F.mem_ends.mp ht).1
            rcases via ht with eq|p
            · exact (vr (eq.symm ▸ htt)).elim
            · exact F.mem_ends.mpr ⟨htt,p⟩
          have read := (F.mem_live.mp hv).1
          obtain ⟨bv,pin⟩ := Finset.mem_filter.mp read
          have vl := Finset.mem_range.mp bv
          have jv := reader_lt F.ao read
          exact (Finset.card_le_card sub).trans
            (ih (F.net.size-v) (by omega) v rfl vl (closed op vl pin))
      · rw [Finset.not_nonempty_iff_eq_empty.mp any]
        decide
  exact all _ g rfl valid hand
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.RootForest
