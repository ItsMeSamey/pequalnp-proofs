import ExactPlaneAffineSparse
import ExactPlaneAffineSubstitution
import Mathlib.LinearAlgebra.AffineSpace.AffineSubspace.Defs
import Mathlib.LinearAlgebra.Finsupp.LinearCombination
import Mathlib.Algebra.CharP.Two
namespace ExactPlaneAffineSpanHit
open ExactPlaneSubsetPolynomial ExactPlaneAffineSparse ExactPlaneAffineSubstitution
open scoped BigOperators
variable {J : Type*} [Fintype J] [DecidableEq J]
abbrev Vec (J : Type*) := J→ZMod 2
noncomputable def support (p : Vec J) : Finset J := Finset.univ.filter (fun j => p j=1)

private theorem dbl (x : Vec J) : x+x=0 := by
  funext j; exact CharTwo.add_self_eq_zero (x j)
private theorem neg_eq (x : Vec J) : -x=x := neg_eq_of_add_eq_zero_left (dbl x)

private theorem geometry (S : Finset (Vec J)) (b : Vec J) (hb : b∈S) (x : Vec J) :
    x∈affineSpan (ZMod 2) (S : Set (Vec J)) ↔
      ∃ T : Finset ↥S,chart b (fun p : ↥S => p.val) T=x := by
  classical
  let diff := fun p : ↥S => p.val-b
  let U := Submodule.span (ZMod 2) (Set.range diff)
  constructor
  · intro hx
    have gen : x-b∈U := by
      apply affineSpan_induction (p:=fun x => x-b∈U) hx
      · intro y hy
        exact Submodule.subset_span ⟨⟨y,hy⟩,rfl⟩
      · intro c u v w hu hv hw
        change c • (u-v)+w-b∈U
        have mem := U.add_mem (U.smul_mem c (U.sub_mem hu hv)) hw
        rw [show (u-b)-(v-b)=u-v by abel] at mem
        convert mem using 1 <;> abel_nf
    obtain ⟨a,ha⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 2)).mp gen
    let T := Finset.univ.filter (fun i : ↥S => a i=1)
    have coeff (i : ↥S) : (if a i=1 then i.val+b else 0)=a i • diff i := by
      have bit : ∀ z : ZMod 2,z=0 ∨ z=1 := by decide
      rcases bit (a i) with z|z <;> simp [z,diff,sub_eq_add_neg,neg_eq]
    refine ⟨T,?_⟩
    unfold chart
    rw [show (∑ i∈T,(i.val+b))=x-b by
      rw [Finset.sum_filter]; exact (Finset.sum_congr rfl (fun i _ => coeff i)).trans ha]
    abel
  · rintro ⟨T,rfl⟩
    have baseMem := mem_affineSpan (ZMod 2) (show b∈(S:Set (Vec J)) from hb)
    induction T using Finset.induction_on with
    | empty => simpa [chart] using baseMem
    | @insert i T hi ih =>
      have elem := mem_affineSpan (ZMod 2) (show i.val∈(S:Set (Vec J)) from i.property)
      have ans := (affineSpan (ZMod 2) (S:Set (Vec J))).smul_vsub_vadd_mem (1:ZMod 2) (p₁:=i.val) (p₂:=b) (p₃:=chart b (fun p : ↥S => p.val) T) elem baseMem ih
      change (1:ZMod 2) • (i.val-b)+chart b (fun p : ↥S => p.val) T∈_ at ans
      simpa [chart,hi,sub_eq_add_neg,neg_eq,add_assoc,add_comm,add_left_comm] using ans

/-- An ambient quartic on finite binary vectors that is nonzero somewhere
on the affine span is nonzero at an odd sum of at most five supplied points.
The resulting sum lies in that same affine span. -/
theorem quartic_span_hit (S : Finset (Vec J)) (c : Coeff J) (degree : degreeLE 4 c)
    (hit : ∃ x∈affineSpan (ZMod 2) (S:Set (Vec J)),eval c (support x)≠0) :
    ∃ l : List (Vec J),(∀ x∈l,x∈S) ∧ (l.length=1 ∨ l.length=3 ∨ l.length=5) ∧
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
  refine ⟨l,inside,?_,(geometry S b hb _).mpr ⟨U,eq.symm⟩,?_⟩
  · split at len <;> omega
  · rw [eq,←score]
    exact hot

#print axioms quartic_span_hit
end ExactPlaneAffineSpanHit
