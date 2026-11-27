import ExactPlaneAffineSpanHit
import Batteries.Tactic.OpenPrivate
import Batteries.Tactic.OpenPrivate
namespace ExactPlaneAffineSpanHit
open ExactPlaneSubsetPolynomial ExactPlaneAffineSparse ExactPlaneAffineSubstitution
open private geometry dbl from ExactPlaneAffineSpanHit
variable {J : Type*} [Fintype J] [DecidableEq J]
theorem degree_span_hit (D : Nat) (S : Finset (Vec J)) (c : Coeff J) (degree : degreeLE D c)
    (hit : ∃ x∈affineSpan (ZMod 2) (S:Set (Vec J)),eval c (support x)≠0) :
    ∃ l : List (Vec J),(∀ x∈l,x∈S) ∧ l.length%2=1 ∧ l.length≤2*(D/2)+1 ∧
      l.sum∈affineSpan (ZMod 2) (S:Set (Vec J)) ∧ eval c (support l.sum)≠0 := by
  classical
  obtain ⟨x,hx,hit⟩ := hit
  have has : S.Nonempty := (affineSpan_nonempty (ZMod 2)).mp ⟨x,hx⟩
  obtain ⟨b,hb⟩ := has
  let p := fun i : ↥S => i.val
  obtain ⟨T,cover⟩ := (geometry S b hb x).mp hx
  obtain ⟨a,da,rep⟩ := explicit_pullback c degree b (fun j (i : ↥S) => i.val j+b j)
  have score (U : Finset ↥S) : eval a U=eval c (support (chart b p U)) := by
    rw [rep]
    apply congrArg (eval c)
    ext j
    simp [support,chart,p,Finset.sum_apply]
  obtain ⟨U,small,hot⟩ := exists_small_nonzero da
    ⟨T,by rw [score,cover]; exact hit⟩
  obtain ⟨l,inside,odd,len,eq⟩ := chart_decode b (dbl b) p (S:Set (Vec J)) hb
    (fun i => i.property) U
  refine ⟨l,inside,odd,?_,(geometry S b hb _).mpr ⟨U,eq.symm⟩,?_⟩
  · split at len <;> omega
  · rw [eq,←score]
    exact hot

#print axioms degree_span_hit
end ExactPlaneAffineSpanHit
