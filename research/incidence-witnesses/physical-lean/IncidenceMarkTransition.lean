import ProtectedIncidenceMoments
namespace IncidenceMarkTransition
variable {α : Type*} [DecidableEq α]

def reserve (M : Finset α) (G : α→Finset α) := M ∪ M.biUnion G

structure Safe (N : α→Finset α) (live M : Finset α) (G : α→Finset α) : Prop where
  inside : M⊆live
  saved : ∀x∈M,G x⊆live ∩ N x
  triple : ∀x∈M,(G x).card=3
  unmarked : ∀x∈live,x∉M → 27≤(live ∩ N x).card

theorem transition (N : α→Finset α) (live M : Finset α) (G : α→Finset α)
    (prior : Safe N live M G) (D : Finset α) (avoid : Disjoint D (reserve M G))
    (small : D.card≤24) :
    let next := live \ D
    let marks := M ∪ next.filter (fun x=>(next ∩ N x).card≤26)
    ∃ G' : α→Finset α, (∀x∈M,G' x=G x) ∧ Safe N next marks G' ∧
      reserve M G⊆reserve marks G' ∧
      ∀x∈live,x∉M → 3≤(next ∩ N x).card := by
  classical
  let next := live \ D
  let danger := next.filter (fun x=>(next ∩ N x).card≤26)
  let marks := M ∪ danger
  have keep {x} (hx : x∈reserve M G) : x∉D := fun hd=>Finset.disjoint_left.mp avoid hd hx
  have old (x) (hx : x∈M) : x∈next :=
    Finset.mem_sdiff.mpr ⟨prior.inside hx,keep (Finset.mem_union_left _ hx)⟩
  have three (x) (hx : x∈live) (un : x∉M) : 3≤(next ∩ N x).card := by
    have h := prior.unmarked x hx un
    have eq : (live ∩ N x) \ D=next ∩ N x := by ext y; simp [next,and_assoc,and_left_comm,and_comm]
    have a : (live ∩ N x).card≤((live ∩ N x) \ D).card+D.card := Finset.card_le_card_sdiff_add_card
    rw [eq] at a
    omega
  let G' := fun x=>if x∈M then G x else
    if h : 3≤(next ∩ N x).card then (Finset.exists_subset_card_eq h).choose else ∅
  have fixed (x) (hx : x∈M) : G' x=G x := by simp [G',hx]
  have assign (x) (hx : x∈marks) : G' x⊆next ∩ N x ∧ (G' x).card=3 := by
    by_cases inM : x∈M
    · rw [fixed x inM]
      refine ⟨?_,prior.triple x inM⟩
      intro y hy
      have nb := Finset.mem_inter.mp (prior.saved x inM hy)
      have prot : y∈reserve M G := Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨x,inM,hy⟩)
      exact Finset.mem_inter.mpr ⟨Finset.mem_sdiff.mpr ⟨nb.1,keep prot⟩,nb.2⟩
    · have outside := Finset.mem_filter.mp ((Finset.mem_union.mp hx).resolve_left inM)
      have tr := three x (Finset.mem_sdiff.mp outside.1).1 inM
      simpa [G',inM,tr] using (Finset.exists_subset_card_eq tr).choose_spec
  refine ⟨G',fixed,?_,?_,three⟩
  · constructor
    · intro x hx
      rcases Finset.mem_union.mp hx with h|h
      · exact old x h
      · exact (Finset.mem_filter.mp h).1
    · exact fun x hx=>(assign x hx).1
    · exact fun x hx=>(assign x hx).2
    · intro x hx h
      by_contra low
      exact h (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hx,by omega⟩))
  · intro x hx
    rcases Finset.mem_union.mp hx with a|a
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ a)
    · obtain ⟨k,hk,xk⟩ := Finset.mem_biUnion.mp a
      exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr
        ⟨k,Finset.mem_union_left _ hk,(fixed k hk).symm ▸ xk⟩)

theorem marked_low (N : α→Finset α) (live M D : Finset α)
    (prev : ∀x∈M,(live ∩ N x).card≤26) :
    let next := live \ D
    ∀x∈ M ∪ next.filter (fun x=>(next ∩ N x).card≤26), (next ∩ N x).card≤26 := by
  intro next x hx
  rcases Finset.mem_union.mp hx with old|fresh
  · apply le_trans (Finset.card_le_card ?_) (prev x old)
    intro y hy
    have e := Finset.mem_inter.mp hy
    exact Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp e.1).1,e.2⟩
  · exact (Finset.mem_filter.mp fresh).2

theorem guard_count401 (N : α→Finset α) (univ removed M : Finset α) (G : α→Finset α)
    (before : ∀x∈M,N x⊆univ) (degree : ∀x∈M,(N x).card=402)
    (low : ∀x∈M,((univ \ removed) ∩ N x).card≤26)
    (codegree : ∀x∈M,∀y∈M,x≠y → (N x∩N y).card≤1) (budget : removed.card≤38808)
    (three : ∀x∈M,(G x).card=3) : (reserve M G).card≤564 := by
  have left (x) (hx : x∈M) : 376≤(removed ∩ N x).card := by
    have eq : N x \ (removed ∩ N x)=(univ \ removed) ∩ N x := by
      ext y
      by_cases h : y∈N x
      · simp [h,before x hx h]
      · simp [h]
    have a : (N x).card≤(N x \ (removed ∩ N x)).card+(removed ∩ N x).card :=
      Finset.card_le_card_sdiff_add_card
    rw [eq,degree x hx] at a
    have b := low x hx
    omega
  have separated (x) (hx : x∈M) (y) (hy : y∈M) (ne : x≠y) :
      (removed ∩ (N x∩N y)).card≤1 :=
    (Finset.card_le_card Finset.inter_subset_right).trans (codegree _ hx _ hy ne)
  have caps := ProtectedIncidenceMoments.marks_401 N M removed left separated budget
  have sums : ∑x∈M,(G x).card=M.card*3 := by
    calc
      _ = ∑x∈M,3 := Finset.sum_congr rfl three
      _ = _ := by simp
  have side : (M.biUnion G).card≤M.card*3 := Finset.card_biUnion_le.trans_eq sums
  have both := Finset.card_union_le M (M.biUnion G)
  change (M∪M.biUnion G).card≤564
  omega
#print axioms transition
#print axioms guard_count401
end IncidenceMarkTransition
