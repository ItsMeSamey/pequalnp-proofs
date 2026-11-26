import Research.NatIncidenceRows
import Research.DeletionPacking
import Research.IncidenceMoments

namespace AdaptiveGeometry

open NatIncidenceRows
open IncidenceRobust (Vertex)

variable {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

noncomputable def neighbors (a : ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n+n)).filter (Edge I a)

noncomputable def bad (D : Finset ℕ) : Finset ℕ := by
  classical
  exact (Finset.range (n+n)).filter (fun a => ((neighbors I a) \ D).card ≤ 1)

omit [DecidableRel I] in
theorem mem_neighbors {a c : ℕ} : c ∈ neighbors I a ↔ c < n+n ∧ Edge I a c := by
  classical
  simp [neighbors]

omit [DecidableRel I] in
theorem mem_bad {D : Finset ℕ} {a : ℕ} :
    a ∈ bad I D ↔ a < n+n ∧ ((neighbors I a) \ D).card ≤ 1 := by
  classical
  simp [bad]

omit [DecidableRel I] in
theorem bad_mono {D E : Finset ℕ} (sub : D ⊆ E) : bad I D ⊆ bad I E := by
  intro a ha
  obtain ⟨lt,h⟩ := (mem_bad I).mp ha
  apply (mem_bad I).mpr
  refine ⟨lt, le_trans (Finset.card_le_card ?_) h⟩
  intro c hc
  exact Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp hc).1,fun hd => (Finset.mem_sdiff.mp hc).2 (sub hd)⟩

omit [DecidableRel I] in
theorem has_neighbor {D : Finset ℕ} {a : ℕ} (ha : a < n+n) (ok : a ∉ bad I D) :
    ∃ c < n+n, c ∉ D ∧ Edge I a c := by
  have big : 1 < ((neighbors I a) \ D).card := by
    by_contra! h
    exact ok ((mem_bad I).mpr ⟨ha,h⟩)
  obtain ⟨c,hc⟩ := Finset.card_pos.mp (lt_trans Nat.zero_lt_one big)
  obtain ⟨yes,keep⟩ := Finset.mem_sdiff.mp hc
  have e := (mem_neighbors I).mp yes
  exact ⟨c,e.1,keep,e.2⟩

variable (degree : ∀ l, Fintype.card {p // I p l} = q+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)

include degree unique in
theorem neighbor_card (hq : 0 < q) (hn : n=q^2+q+1) {a : ℕ} (ha : a < n+n) :
    (neighbors I a).card = q+1 := by
  classical
  obtain ⟨v,rfl⟩ := decode ha
  cases v with
  | inl p =>
    let f : Fin n ↪ ℕ := ⟨fun l => n+l.val,fun _ _ e => Fin.ext (Nat.add_left_cancel e)⟩
    have eq : neighbors I (encode (.inl p)) = (IncidenceRobust.lines I p).map f := by
      ext c
      constructor
      · intro h
        obtain ⟨lt,e⟩ := (mem_neighbors I).mp h
        obtain ⟨w,rfl⟩ := decode lt
        have h := (edge_encode I _ w).mp e
        cases w with
        | inl x => exact False.elim h
        | inr l => exact Finset.mem_map.mpr ⟨l,by simpa [IncidenceRobust.lines,IncidenceRobust.Edge] using h,rfl⟩
      · intro h
        obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp h
        apply (mem_neighbors I).mpr
        exact ⟨encode_lt (Sum.inr l : Vertex n),(edge_encode I _ (.inr l)).mpr ((Finset.mem_filter.mp hl).2)⟩
    rw [eq,Finset.card_map,IncidenceRobust.lines_card I degree unique hq hn]
  | inr l =>
    let f : Fin n ↪ ℕ := ⟨Fin.val,fun _ _ e => Fin.ext e⟩
    have eq : neighbors I (encode (.inr l)) = (IncidenceRobust.points I l).map f := by
      ext c
      constructor
      · intro h
        obtain ⟨lt,e⟩ := (mem_neighbors I).mp h
        obtain ⟨w,rfl⟩ := decode lt
        have h := (edge_encode I _ w).mp e
        cases w with
        | inr x => exact False.elim h
        | inl p => exact Finset.mem_map.mpr ⟨p,by simpa [IncidenceRobust.points,IncidenceRobust.Edge] using h,rfl⟩
      · intro h
        obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp h
        exact (mem_neighbors I).mpr ⟨encode_lt (.inl p : Vertex n),
          (edge_encode I _ (.inl p)).mpr ((Finset.mem_filter.mp hp).2)⟩
    rw [eq,Finset.card_map,IncidenceRobust.points_card I degree]

include unique in
omit [DecidableRel I] in
private theorem codegree_aux (a b c d : Vertex n) (ab : a ≠ b)
    (ac : IncidenceRobust.Edge I a c) (ad : IncidenceRobust.Edge I a d)
    (bc : IncidenceRobust.Edge I b c) (bd : IncidenceRobust.Edge I b d) : c=d := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp only [IncidenceRobust.Edge] at *
  · rename_i p r l k
    obtain ⟨_,_,only⟩ := unique p r (fun h => ab (h ▸ rfl))
    exact congrArg Sum.inr ((only l ⟨ac,bc⟩).trans (only k ⟨ad,bd⟩).symm)
  · rename_i l k p r
    by_contra ne
    obtain ⟨_,_,only⟩ := unique p r (fun h => ne (h ▸ rfl))
    exact ab (congrArg Sum.inr ((only l ⟨ac,ad⟩).trans (only k ⟨bc,bd⟩).symm))

include unique in
omit [DecidableRel I] in
theorem codegree {a b : ℕ} (ha : a<n+n) (hb : b<n+n) (ab : a ≠ b) :
    (neighbors I a ∩ neighbors I b).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro c hc d hd
  obtain ⟨ac,bc⟩ := Finset.mem_inter.mp hc
  obtain ⟨ad,bd⟩ := Finset.mem_inter.mp hd
  obtain ⟨cc,ac⟩ := (mem_neighbors I).mp ac
  obtain ⟨dd,ad⟩ := (mem_neighbors I).mp ad
  obtain ⟨_,bc⟩ := (mem_neighbors I).mp bc
  obtain ⟨_,bd⟩ := (mem_neighbors I).mp bd
  obtain ⟨a,rfl⟩ := decode ha
  obtain ⟨b,rfl⟩ := decode hb
  obtain ⟨c,rfl⟩ := decode cc
  obtain ⟨d,rfl⟩ := decode dd
  exact congrArg encode (codegree_aux I unique a b c d (fun h => ab (h ▸ rfl))
    ((edge_encode I _ _).mp ac) ((edge_encode I _ _).mp ad)
    ((edge_encode I _ _).mp bc) ((edge_encode I _ _).mp bd))

omit [DecidableRel I] in
private theorem no_triangle {a b c : ℕ} (ab : Edge I a b) (ac : Edge I a c) : ¬Edge I b c := by
  obtain ⟨x,y,rfl,rfl,e⟩ := ab
  obtain ⟨x',z,h,rfl,e'⟩ := ac
  have eq := encode_inj h
  subst x'
  rw [edge_encode]
  cases x <;> cases y <;> cases z <;> simp_all [IncidenceRobust.Edge]

include unique in
omit [DecidableRel I] in
private theorem distinguish_from {D : Finset ℕ} {a b : ℕ} (ha : a<n+n) (hb : b<n+n)
    (ab : a ≠ b) (good : a ∉ bad I D) :
    ∃ c < n+n, c ∉ D ∧ c ≠ a ∧ c ≠ b ∧ Edge I a c ∧ ¬Edge I b c := by
  have size : 1 < ((neighbors I a) \ D).card := by
    by_contra! small
    exact good ((mem_bad I).mpr ⟨ha,small⟩)
  obtain ⟨c,hc,d,hd,cd⟩ := Finset.one_lt_card.mp size
  obtain ⟨ca,ck⟩ := Finset.mem_sdiff.mp hc
  obtain ⟨da,dk⟩ := Finset.mem_sdiff.mp hd
  obtain ⟨cl,ce⟩ := (mem_neighbors I).mp ca
  obtain ⟨dl,de⟩ := (mem_neighbors I).mp da
  have cne : c ≠ a := fun h => edge_self I a (h ▸ ce)
  have dne : d ≠ a := fun h => edge_self I a (h ▸ de)
  by_cases cb : c=b
  · exact ⟨d,dl,dk,dne,by omega,de,no_triangle I (cb ▸ ce) de⟩
  by_cases db : d=b
  · exact ⟨c,cl,ck,cne,cb,ce,no_triangle I (db ▸ de) ce⟩
  by_cases covered : Edge I b c
  · refine ⟨d,dl,dk,dne,db,de,?_⟩
    intro also
    exact cd (Finset.card_le_one.mp (codegree I unique ha hb ab) c
      (Finset.mem_inter.mpr ⟨ca,(mem_neighbors I).mpr ⟨cl,covered⟩⟩) d
      (Finset.mem_inter.mpr ⟨da,(mem_neighbors I).mpr ⟨dl,also⟩⟩))
  · exact ⟨c,cl,ck,cne,cb,ce,covered⟩

include unique in
omit [DecidableRel I] in
theorem distinguish {D : Finset ℕ} {a b : ℕ} (ha : a<n+n) (hb : b<n+n) (ab : a ≠ b)
    (good : ¬(a ∈ bad I D ∧ b ∈ bad I D)) :
    ∃ c < n+n, c ∉ D ∧ c ≠ a ∧ c ≠ b ∧
    ((Edge I a c ∧ ¬Edge I b c) ∨ (Edge I b c ∧ ¬Edge I a c)) := by
  by_cases h : a ∈ bad I D
  · obtain ⟨c,lt,ok,cb,ca,ea⟩ := distinguish_from I unique hb ha ab.symm (fun t => good ⟨h,t⟩)
    exact ⟨c,lt,ok,ca,cb,Or.inr ea⟩
  · obtain ⟨c,lt,ok,ca,cb,ea⟩ := distinguish_from I unique ha hb ab h
    exact ⟨c,lt,ok,ca,cb,Or.inl ea⟩

include degree unique in
private theorem many (hq : 0<q) (hn : n=q^2+q+1) {D : Finset ℕ} {a : ℕ} (h : a ∈ bad I D) :
    q ≤ (neighbors I a ∩ D).card := by
  have b := (mem_bad I).mp h
  have total := Finset.card_sdiff_add_card_inter (neighbors I a) D
  have deg := neighbor_card I degree unique hq hn b.1
  omega

include degree unique in
theorem card_bad (hq : 0<q) (hn : n=q^2+q+1) (D : Finset ℕ) (small : 2*D.card < q^2+q) :
    (bad I D).card < q := by
  apply DeletionPacking.few_depleted (neighbors I) D _ q small (fun a ha => many I degree unique hq hn ha)
  exact fun _ ha _ hb ne => codegree I unique ((mem_bad I).mp ha).1 ((mem_bad I).mp hb).1 ne

include degree unique in
theorem moment_bad (hq : 0<q) (hn : n=q^2+q+1) (D : Finset ℕ) :
    q^2*(bad I D).card^2 ≤ D.card*(bad I D).card*(q+(bad I D).card) := by
  apply IncidenceMoments.packing (neighbors I) (bad I D) D q
  · intro a ha
    simpa [Finset.inter_comm] using many I degree unique hq hn ha
  · intro a ha
    rw [← neighbor_card I degree unique hq hn ((mem_bad I).mp ha).1]
    exact Finset.card_le_card Finset.inter_subset_right
  · intro a ha b hb ne
    exact le_trans (Finset.card_le_card Finset.inter_subset_right)
      (codegree I unique ((mem_bad I).mp ha).1 ((mem_bad I).mp hb).1 ne)

end AdaptiveGeometry
