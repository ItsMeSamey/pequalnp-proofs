import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Tactic.Ring

namespace IncidenceRobust

variable {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]

def points (l : Fin n) := Finset.univ.filter (fun p => I p l)
def lines (p : Fin n) := Finset.univ.filter (fun l => I p l)

variable (degree : ∀ l, Fintype.card {p // I p l} = q+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)

include degree in
theorem points_card (l : Fin n) : (points I l).card = q+1 := by
  simpa [Fintype.card_subtype,points] using degree l

include degree unique in
theorem lines_card (hq : 0 < q) (hn : n = q^2+q+1) (p : Fin n) :
    (lines I p).card = q+1 := by
  let F := fun l => (points I l).erase p
  have size (l) (hl : l ∈ lines I p) : (F l).card = q := by
    have inc : p ∈ points I l := by simpa [points,lines] using hl
    simp [F, Finset.card_erase_of_mem inc,points_card I degree]
  have disj : (lines I p : Set (Fin n)).PairwiseDisjoint F := by
    intro l hl k hk ne
    apply Finset.disjoint_left.mpr
    intro a hal hak
    obtain ⟨ap,al⟩ := Finset.mem_erase.mp hal
    obtain ⟨_,ak⟩ := Finset.mem_erase.mp hak
    obtain ⟨_,_,only⟩ := unique p a ap.symm
    apply ne
    exact (only l ⟨(Finset.mem_filter.mp hl).2,(Finset.mem_filter.mp al).2⟩).trans
      (only k ⟨(Finset.mem_filter.mp hk).2,(Finset.mem_filter.mp ak).2⟩).symm
  have covers : (lines I p).biUnion F = Finset.univ.erase p := by
    ext a
    constructor
    · intro h
      obtain ⟨l,_,hl⟩ := Finset.mem_biUnion.mp h
      exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hl).1,Finset.mem_univ _⟩
    · intro h
      have ap := (Finset.mem_erase.mp h).1
      obtain ⟨l,⟨pl,al⟩,_⟩ := unique p a ap.symm
      exact Finset.mem_biUnion.mpr ⟨l,by simpa [lines] using pl,
        Finset.mem_erase.mpr ⟨ap,by simpa [points] using al⟩⟩
  have h := Finset.card_biUnion disj
  rw [covers,Finset.card_erase_of_mem (Finset.mem_univ _),Finset.card_univ,Fintype.card_fin,
    Finset.sum_congr rfl size,Finset.sum_const] at h
  have eql : (q+1)*q = (lines I p).card*q := by
    change n-1 = (lines I p).card * q at h
    have hh : n-1=q^2+q := by omega
    rw [hh] at h
    rw [Nat.add_mul, Nat.one_mul, ← Nat.pow_two]
    exact h
  exact (Nat.eq_of_mul_eq_mul_right hq eql).symm

include unique in
theorem line_overlap {a b : Fin n} (ab : a ≠ b) :
    ((lines I a) ∩ (lines I b)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro l hl k hk
  obtain ⟨_,_,only⟩ := unique a b ab
  simp only [lines,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at hl hk
  exact (only l hl).trans (only k hk).symm

include unique in
theorem point_overlap {l k : Fin n} (lk : l ≠ k) :
    ((points I l) ∩ (points I k)).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  by_contra ne
  obtain ⟨_,_,only⟩ := unique a b ne
  simp only [points,Finset.mem_inter,Finset.mem_filter,Finset.mem_univ,true_and] at ha hb
  exact lk ((only l ⟨ha.1,hb.1⟩).trans (only k ⟨ha.2,hb.2⟩).symm)

abbrev Vertex (n : ℕ) := Fin n ⊕ Fin n

def Edge : Vertex n → Vertex n → Prop
  | .inl p, .inr l => I p l
  | .inr l, .inl p => I p l
  | _, _ => False

def candidates : Vertex n → Vertex n → Finset (Vertex n)
  | .inl p, .inl r => (lines I p \ lines I r).map Function.Embedding.inr
  | .inl p, .inr l => ((lines I p).erase l).map Function.Embedding.inr
  | .inr l, .inl p => ((points I l).erase p).map Function.Embedding.inl
  | .inr l, .inr k => (points I l \ points I k).map Function.Embedding.inl

theorem candidate_spec {a b c : Vertex n} (hc : c ∈ candidates I a b) :
    Edge I a c ∧ ¬ Edge I b c ∧ c ≠ a ∧ c ≠ b := by
  cases a <;> cases b <;>
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hc <;>
    simp_all [Edge,Function.Embedding.inl,Function.Embedding.inr,lines,points] <;> change _ at hi <;> first | exact hi | exact ⟨hi.2,fun e => hi.1 (Sum.inr.inj e)⟩ | exact ⟨hi.2,fun e => hi.1 (Sum.inl.inj e)⟩

include degree unique in
theorem candidates_card (hq : 0 < q) (hn : n = q^2+q+1) {a b : Vertex n} (ab : a ≠ b) :
    q ≤ (candidates I a b).card := by
  cases a with
  | inl p =>
    cases b with
    | inl r =>
      have h := line_overlap I unique (show p ≠ r from fun h => ab (h ▸ rfl))
      have c := Finset.card_sdiff_add_card_inter (lines I p) (lines I r)
      have d := lines_card I degree unique hq hn p
      simp only [candidates,Finset.card_map]; omega
    | inr l =>
      have d := lines_card I degree unique hq hn p
      simp only [candidates,Finset.card_map]
      by_cases mem : l ∈ lines I p <;> simp [mem,d]
  | inr l =>
    cases b with
    | inl p =>
      have d := points_card I degree l
      simp only [candidates,Finset.card_map]
      by_cases mem : p ∈ points I l <;> simp [mem,d]
    | inr k =>
      have h := point_overlap I unique (show l ≠ k from fun h => ab (h ▸ rfl))
      have c := Finset.card_sdiff_add_card_inter (points I l) (points I k)
      have d := points_card I degree l
      simp only [candidates,Finset.card_map]; omega

include degree unique in
theorem distinguish (hq : 0 < q) (hn : n = q^2+q+1) (D : Finset (Vertex n))
    (small : D.card < 2*q) {a b : Vertex n} (ab : a ≠ b) :
    ∃ c ∉ D, c ≠ a ∧ c ≠ b ∧
      ((Edge I a c ∧ ¬ Edge I b c) ∨ (Edge I b c ∧ ¬ Edge I a c)) := by
  let A := candidates I a b
  let B := candidates I b a
  have disj : Disjoint A B := Finset.disjoint_left.mpr fun _ ha hb =>
    (candidate_spec I ha).2.1 (candidate_spec I hb).1
  have card := Finset.card_union_of_disjoint disj
  have ca := candidates_card I degree unique hq hn ab
  have cb := candidates_card I degree unique hq hn ab.symm
  change q ≤ A.card at ca
  change q ≤ B.card at cb
  have ns : ¬ A ∪ B ⊆ D := fun sub => by have := Finset.card_le_card sub; omega
  obtain ⟨c,hc,out⟩ := Finset.not_subset.mp ns
  rcases Finset.mem_union.mp hc with ha | hb
  · obtain ⟨e,ne,na,nb⟩ := candidate_spec I ha
    exact ⟨c,out,na,nb,Or.inl ⟨e,ne⟩⟩
  · obtain ⟨e,ne,nb,na⟩ := candidate_spec I hb
    exact ⟨c,out,na,nb,Or.inr ⟨e,ne⟩⟩

include degree unique in
theorem has_neighbor (hq : 0 < q) (hn : n = q^2+q+1) (D : Finset (Vertex n))
    (small : D.card ≤ q) (a : Vertex n) : ∃ c ∉ D, Edge I a c := by
  cases a with
  | inl p =>
    let S : Finset (Vertex n) := (lines I p).map Function.Embedding.inr
    have d : S.card = q+1 := by simpa [S] using lines_card I degree unique hq hn p
    have ns : ¬ S ⊆ D := fun sub => by have := Finset.card_le_card sub; omega
    obtain ⟨c,hc,out⟩ := Finset.not_subset.mp ns
    obtain ⟨l,hl,rfl⟩ := Finset.mem_map.mp hc
    exact ⟨_,out,(Finset.mem_filter.mp hl).2⟩
  | inr l =>
    let S : Finset (Vertex n) := (points I l).map Function.Embedding.inl
    have d : S.card = q+1 := by simpa [S] using points_card I degree l
    have ns : ¬ S ⊆ D := fun sub => by have := Finset.card_le_card sub; omega
    obtain ⟨c,hc,out⟩ := Finset.not_subset.mp ns
    obtain ⟨p,hp,rfl⟩ := Finset.mem_map.mp hc
    exact ⟨_,out,(Finset.mem_filter.mp hp).2⟩

end IncidenceRobust
