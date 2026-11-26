import ExactPlaneSubsetPolynomial
import Mathlib.Tactic.Abel
namespace ExactPlaneAffineSparse
open scoped BigOperators
variable {V I A : Type*} [AddCommGroup V] [DecidableEq I]

def chart (base : V) (point : I→V) (J : Finset I) : V :=
  base+∑ i∈J,(point i+base)

def oddList (base : V) (xs : List V) : List V :=
  if xs.length%2=0 then base::xs else xs

theorem oddList_sum (base : V) (two : base+base=0) (xs : List V) :
    base+(xs.map (fun x=>x+base)).sum=(oddList base xs).sum := by
  induction xs with
  | nil => simp [oddList]
  | cons x xs ih =>
    simp only [List.map_cons,List.sum_cons]
    calc
      _ = x+base+(base+(xs.map (fun v=>v+base)).sum) := by abel
      _ = x+base+(oddList base xs).sum := by rw [ih]
      _ = (oddList base (x::xs)).sum := by
        by_cases even : xs.length%2=0
        · have next : (xs.length+1)%2≠0 := by omega
          simp only [oddList,List.length_cons,even,next,if_true,if_false,if_pos,if_neg,List.sum_cons]
          calc
            _ = x+(base+base)+xs.sum := by abel
            _ = _ := by rw [two,add_zero]
        · have next : (xs.length+1)%2=0 := by omega
          simp only [oddList,List.length_cons,even,next,if_true,if_false,if_pos,if_neg,List.sum_cons]
          abel

theorem chart_decode (base : V) (two : base+base=0) (point : I→V)
    (S : Set V) (hb : base∈S) (hs : ∀ i,point i∈S) (J : Finset I) :
    ∃ l : List V,(∀ x∈l,x∈S) ∧ l.length%2=1 ∧
      l.length=(if J.card%2=0 then J.card+1 else J.card) ∧ l.sum=chart base point J := by
  classical
  let xs := J.toList.map point
  have len : xs.length=J.card := by simp [xs]
  refine ⟨oddList base xs,?_,?_,?_,?_⟩
  · intro x hx
    have all (j) (hj : j∈xs) : j∈S := by
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hj
      exact hs i
    by_cases e : xs.length%2=0
    · rw [oddList,if_pos e] at hx
      rcases List.mem_cons.mp hx with rfl|h
      · exact hb
      · exact all _ h
    · exact all _ (by simpa [oddList,e] using hx)
  · by_cases e : xs.length%2=0 <;> simp only [oddList,e,if_true,if_false,if_pos,if_neg,List.length_cons] <;> omega
  · simp only [oddList,len]
    split <;> simp [len]
  · rw [←oddList_sum base two xs]
    simp [xs,chart,List.map_map,Function.comp_def]

theorem quartic_hit [AddCommMonoid A] (base : V) (two : base+base=0)
    (point : I→V) (S : Set V) (hb : base∈S) (hs : ∀ i,point i∈S)
    (score : V→A) (c : Finset I→A) (deg : ExactPlaneSubsetPolynomial.degreeLE 4 c)
    (rep : ∀ J,score (chart base point J)=ExactPlaneSubsetPolynomial.eval c J)
    (hit : ∃ J,score (chart base point J)≠0) :
    ∃ l : List V,(∀ x∈l,x∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧ score l.sum≠0 := by
  obtain ⟨J,hJ⟩ := hit
  obtain ⟨T,cap,nonzero⟩ := ExactPlaneSubsetPolynomial.exists_small_nonzero deg
    ⟨J,fun h => hJ ((rep J).trans h)⟩
  obtain ⟨l,inside,odd,len,eq⟩ := chart_decode base two point S hb hs T
  refine ⟨l,inside,?_,?_⟩
  · split at len <;> omega
  · rw [eq,rep]
    exact nonzero

/-- Covering a search domain is enough. An independent affine basis is optional. -/
theorem covered_hit [AddCommMonoid A] (base : V) (two : base+base=0)
    (point : I→V) (S domain : Set V) (hb : base∈S) (hs : ∀ i,point i∈S)
    (score : V→A) (c : Finset I→A) (deg : ExactPlaneSubsetPolynomial.degreeLE 4 c)
    (rep : ∀ J,score (chart base point J)=ExactPlaneSubsetPolynomial.eval c J)
    (cover : ∀ x∈domain,∃ J,chart base point J=x) (hit : ∃ x∈domain,score x≠0) :
    ∃ l : List V,(∀ x∈l,x∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧ score l.sum≠0 := by
  obtain ⟨x,hx,nz⟩ := hit
  obtain ⟨J,eq⟩ := cover x hx
  exact quartic_hit base two point S hb hs score c deg rep ⟨J,eq.symm ▸ nz⟩
#print axioms quartic_hit
#print axioms covered_hit
end ExactPlaneAffineSparse
