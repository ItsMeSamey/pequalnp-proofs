import ThresholdAnchorEnumeration
import ThresholdGraphPostorder
namespace ThresholdPeelSchedule
variable {V : Type*} [Fintype V] [DecidableEq V] {m : Nat} (G : SimpleGraph V)
    [Fintype G.ConnectedComponent] (j : V ↪ Fin m)

theorem star_remote_schedule (u : V) (S : G.ConnectedComponent → Finset V)
    (loc : ∀ c v, v∈S c → G.connectedComponentMk v=c)
    (remote : ∀ c, c≠G.connectedComponentMk u → ∃ a b, G.Adj a b ∧ S c={a,b})
    (f : Pins m → Bool) (x z : Pins m) (xs : x⊆(S (G.connectedComponentMk u)).map j)
    (zs : z⊆(S (G.connectedComponentMk u)).map j) (fx : f x=false) (fz : f z=true)
    (accept : ∀ c, c≠G.connectedComponentMk u → ∀ a b, G.Adj a b → S c={a,b} →
      f (insert (j b) (insert (j a) x))=true) :
    ∃ rs : List (Step m), Scheduled f ((Finset.univ.biUnion S).map j) rs ∧
      ending ((Finset.univ.biUnion S).map j) rs=(S (G.connectedComponentMk u)).map j ∧
      rs.length+1=Fintype.card G.ConnectedComponent := by
  classical
  let root := G.connectedComponentMk u
  let ids := (Finset.univ.erase root).toList
  have mem (c : G.ConnectedComponent) : c∈ids ↔ c≠root := by simp [ids]
  have pick (c : G.ConnectedComponent) : ∃ p : V×V, c≠root →
      G.Adj p.1 p.2 ∧ S c={p.1,p.2} := by
    by_cases h : c=root
    · exact ⟨(u,u),fun ne => (ne h).elim⟩
    · obtain ⟨a,b,e,s⟩ := remote c h
      exact ⟨(a,b),fun _ => ⟨e,s⟩⟩
  choose P spec using pick
  let pair := fun c => (j (P c).1,j (P c).2)
  let center := (S root).map j
  let tag := fun i : Fin m => if h : ∃ v, j v=i then G.connectedComponentMk h.choose else root
  have tagj (v : V) : tag (j v)=G.connectedComponentMk v := by
    have h : ∃ w, j w=j v := ⟨v,rfl⟩
    simp only [tag,dif_pos h,j.injective h.choose_spec]
  have sides (c) (hc : c∈ids) :
      tag (pair c).1=c ∧ tag (pair c).2=c ∧ (pair c).1≠(pair c).2 := by
    obtain ⟨adj,sc⟩ := spec c ((mem c).mp hc)
    exact ⟨(tagj _).trans (loc c _ (by simp [sc])),(tagj _).trans (loc c _ (by simp [sc])),
      fun eq => adj.ne (j.injective eq)⟩
  have both (i : Fin m) : i∈names (ids.map pair) ↔ ∃ c∈ids, i∈(S c).map j := by
    unfold names
    simp only [List.mem_flatMap,List.mem_map,List.mem_cons,List.mem_singleton]
    constructor
    · rintro ⟨_,⟨c,hc,rfl⟩,hit⟩
      obtain ⟨_,sc⟩ := spec c ((mem c).mp hc)
      refine ⟨c,hc,?_⟩
      simpa [pair,sc] using hit
    · rintro ⟨c,hc,hit⟩
      obtain ⟨_,sc⟩ := spec c ((mem c).mp hc)
      exact ⟨pair c,⟨c,hc,rfl⟩,by simpa [pair,sc] using hit⟩
  have eqworld : world center (ids.map pair)=((Finset.univ.biUnion S).map j) := by
    ext i
    simp only [world,Finset.mem_union,List.mem_toFinset,both,Finset.mem_map,Finset.mem_biUnion,
      Finset.mem_univ,true_and,center]
    constructor
    · rintro (⟨v,hv,ev⟩|⟨c,_,v,hv,ev⟩)
      · exact ⟨v,⟨root,hv⟩,ev⟩
      · exact ⟨v,⟨c,hv⟩,ev⟩
    · rintro ⟨v,⟨c,hv⟩,ev⟩
      by_cases eq : c=root
      · subst c; exact Or.inl ⟨v,hv,ev⟩
      · exact Or.inr ⟨c,(mem c).mpr eq,v,hv,ev⟩
  have outside (i) (hi : i∈names (ids.map pair)) : i∉center := by
    obtain ⟨c,hc,hv⟩ := (both i).mp hi
    obtain ⟨v,hv,rfl⟩ := Finset.mem_map.mp hv
    intro h
    have hroot : v∈S root := by simpa [center] using h
    exact (mem c).mp hc ((loc c v (by simpa using hv)).symm.trans (loc root v hroot))
  have nodup := index_names tag pair ids (Finset.nodup_toList _) (fun c h => (sides c h).1)
    (fun c h => (sides c h).2.1) (fun c h => (sides c h).2.2)
  have ready := remote_schedule f center x z xs zs fx fz (ids.map pair) nodup outside
    (by rintro p hp; obtain ⟨c,hc,rfl⟩ := List.mem_map.mp hp
        exact accept c ((mem c).mp hc) _ _ (spec c ((mem c).mp hc)).1 (spec c ((mem c).mp hc)).2)
  rw [eqworld] at ready
  refine ⟨_,ready.1,ready.2,?_⟩
  simp only [List.length_map,ids,Finset.length_toList,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ]
  have pos : 0<Fintype.card G.ConnectedComponent := Fintype.card_pos_iff.mpr ⟨root⟩
  omega
end ThresholdPeelSchedule
