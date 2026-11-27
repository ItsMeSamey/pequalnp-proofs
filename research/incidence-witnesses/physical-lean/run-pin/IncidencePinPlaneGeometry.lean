import Research.IncidenceRobust
import Mathlib.Algebra.Order.BigOperators.Group.Finset
namespace IncidencePinPlaneGeometry
open IncidenceRobust
open scoped BigOperators
variable {q n : Nat} (I : Fin n→Fin n→Prop) [DecidableRel I]
variable (degree : ∀ l,Fintype.card {p // I p l}=q+1)
variable (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
variable (hq : 0<q) (hn : n=q^2+q+1)

def removedLines (P : Finset (Fin n)) := P.biUnion (lines I)

theorem removed_iff (P : Finset (Fin n)) (l : Fin n) :
    l∈removedLines I P ↔ ∃p∈P,I p l := by simp [removedLines,lines]

include degree unique hq hn in
theorem collinear_card (P : Finset (Fin n)) (l : Fin n) (nonempty : P.Nonempty)
    (on : ∀ p∈P,I p l) : (removedLines I P).card=1+q*P.card := by
  let F := fun p => (lines I p).erase l
  have dis : (P : Set (Fin n)).PairwiseDisjoint F := by
    intro a ha b hb ne
    apply Finset.disjoint_left.mpr
    intro k h1 h2
    obtain ⟨kl,x⟩ := Finset.mem_erase.mp h1
    obtain ⟨_,y⟩ := Finset.mem_erase.mp h2
    obtain ⟨_,_,only⟩ := unique a b ne
    exact kl ((only k ⟨(Finset.mem_filter.mp x).2,(Finset.mem_filter.mp y).2⟩).trans
      (only l ⟨on a ha,on b hb⟩).symm)
  have unionEq : removedLines I P=insert l (P.biUnion F) := by
    ext k
    rw [removed_iff,Finset.mem_insert]
    constructor
    · rintro ⟨p,hp,h⟩
      by_cases eq : k=l
      · exact Or.inl eq
      · exact Or.inr (Finset.mem_biUnion.mpr ⟨p,hp,Finset.mem_erase.mpr ⟨eq,by simpa [lines] using h⟩⟩)
    · rintro (rfl|h)
      · obtain ⟨p,hp⟩ := nonempty
        exact ⟨p,hp,on p hp⟩
      · obtain ⟨p,hp,inside⟩ := Finset.mem_biUnion.mp h
        exact ⟨p,hp,(Finset.mem_filter.mp (Finset.mem_erase.mp inside).2).2⟩
  have fresh : l∉P.biUnion F := by simp [F]
  have each (p : Fin n) (hp : p∈P) : (F p).card=q := by
    rw [show F p=(lines I p).erase l from rfl,Finset.card_erase_of_mem (by simpa [lines] using on p hp),
      lines_card I degree unique hq hn]
    omega
  rw [unionEq,Finset.card_insert_of_notMem fresh,Finset.card_biUnion dis,Finset.sum_congr rfl each]
  simp [Nat.mul_comm,Nat.add_comm]

include unique in
theorem lost_at_free_point (P : Finset (Fin n)) (p : Fin n) (free : p∉P) :
    ((lines I p)∩removedLines I P).card≤P.card := by
  let F := fun a => lines I p ∩ lines I a
  have incl : lines I p ∩ removedLines I P ⊆ P.biUnion F := by
    intro l h
    obtain ⟨hp,deleted⟩ := Finset.mem_inter.mp h
    obtain ⟨a,ha,ia⟩ := (removed_iff I P l).mp deleted
    exact Finset.mem_biUnion.mpr ⟨a,ha,Finset.mem_inter.mpr ⟨hp,by simpa [lines] using ia⟩⟩
  calc
    _ ≤ (P.biUnion F).card := Finset.card_le_card incl
    _ ≤ ∑a∈P,(F a).card := Finset.card_biUnion_le
    _ ≤ ∑_a∈P,1 := Finset.sum_le_sum (fun a ha => line_overlap I unique (fun e => free (e ▸ ha)))
    _ = _ := by simp

include degree unique hq hn in
theorem free_point_degree (P : Finset (Fin n)) (p : Fin n) (free : p∉P) :
    q+1-P.card ≤ ((lines I p) \ removedLines I P).card := by
  have h := lost_at_free_point I unique P p free
  have card := Finset.card_sdiff_add_card_inter (lines I p) (removedLines I P)
  rw [lines_card I degree unique hq hn] at card
  omega

include degree in
theorem free_line_degree (P : Finset (Fin n)) (l : Fin n) (free : l∉removedLines I P) :
    ((points I l) \ P).card=q+1 := by
  have eq : points I l \ P=points I l := by
    ext p
    simp only [Finset.mem_sdiff]
    exact ⟨And.left,fun h => ⟨h,fun hp => free ((removed_iff I P l).mpr
      ⟨p,hp,(Finset.mem_filter.mp h).2⟩)⟩⟩
  rw [eq,points_card I degree]

include degree in
theorem survivor_on_line (P : Finset (Fin n)) (small : P.card<q+1) (l : Fin n) :
    ∃ p∉P,I p l := by
  by_contra! no
  have incl : points I l ⊆ P := by
    intro p h
    by_contra not
    exact no p not (Finset.mem_filter.mp h).2
  have bound := Finset.card_le_card incl
  rw [points_card I degree] at bound
  omega

#print axioms collinear_card
#print axioms free_point_degree
#print axioms free_line_degree
end IncidencePinPlaneGeometry
