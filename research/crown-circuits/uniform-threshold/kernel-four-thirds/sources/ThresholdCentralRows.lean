import ThresholdGraphRows
namespace ThresholdGlobalGlue
open ThresholdPeelSchedule
theorem central_rows {V E : Type*} [Fintype V] [DecidableEq V] {m : Nat}
    (G : SimpleGraph V) [DecidableRel G.Adj] (j : V ↪ Fin m) (u : V)
    (ends : E → Pins m) (f : Pins m → Bool) (rows : EdgeRows ends f)
    (edge : ∀ {a b}, G.Adj a b → ∃ e, ends e={j a,j b})
    (large : 2≤G.degree u) :
    ∃ x z : Pins m, x⊆(insert u (G.neighborFinset u)).map j ∧
      z⊆(insert u (G.neighborFinset u)).map j ∧ f x=false ∧ f z=true ∧
      ∀ a b, G.Adj a b → a≠u → b≠u → f (insert (j b) (insert (j a) x))=true := by
  classical
  have h : 1<(G.neighborFinset u).card := by rw [G.card_neighborFinset_eq_degree]; omega
  obtain ⟨w,hw,t,ht,wt⟩ := Finset.one_lt_card.mp h
  have uw := (G.mem_neighborFinset u w).mp hw
  have ut := (G.mem_neighborFinset u t).mp ht
  obtain ⟨e,he⟩ := edge uw
  obtain ⟨d,hd⟩ := edge ut
  have diff : e≠d := by
    intro h
    have hm : j w∈ends d := by rw [←h,he]; simp
    simpa [hd,uw.ne.symm,wt] using hm
  let center := (insert u (G.neighborFinset u)).map j
  have cu : j u ∈ center := Finset.mem_map.mpr ⟨u,by simp,rfl⟩
  have cw : j w ∈ center := Finset.mem_map.mpr ⟨w,by simp [hw],rfl⟩
  have ct : j t ∈ center := Finset.mem_map.mpr ⟨t,by simp [ht],rfl⟩
  have xe : ends e ⊆ center := he ▸ Finset.insert_subset cu (Finset.singleton_subset_iff.mpr cw)
  have xd : ends d ⊆ center := hd ▸ Finset.insert_subset cu (Finset.singleton_subset_iff.mpr ct)
  refine ⟨ends e,ends e∪ends d,xe,Finset.union_subset xe xd,rows.single e,rows.pair e d diff,?_⟩
  intro a b ab au bu
  obtain ⟨r,hr⟩ := edge ab
  have er : e≠r := by
    intro eq
    have hu : j u ∈ ends r := by rw [←eq,he]; simp
    simpa [hr,au.symm,bu.symm] using hu
  have union : ends e ∪ ends r = insert (j b) (insert (j a) (ends e)) := by
    rw [hr]
    ext k
    simp
    tauto
  exact union ▸ rows.pair e r er
end ThresholdGlobalGlue
