import ExactPlaneAffineSpanHit
import Mathlib.Algebra.BigOperators.Group.Finset.Powerset

namespace ExactPlaneCosetDegree
open ExactPlaneSubsetPolynomial ExactPlaneAffineSubstitution ExactPlaneAffineSpanHit
open scoped BigOperators
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]

def coset (b : Vec J) (v : I→Vec J) (A : Finset I) : Vec J := b+∑ i∈A,v i

def derivative (f : Vec J→F) (v x : Vec J) : F := f (x+v)+f x

def HasDegree (f : Vec J→F) (d : ℕ) : Prop :=
  ∃ p : Coeff J, degreeLE d p ∧ ∀ x,eval p (support x)=f x

private theorem pull (b : Vec J) (v : I→Vec J) {f : Vec J→F} {d : ℕ}
    (hf : HasDegree f d) :
    ∃ p : Coeff I, degreeLE d p ∧ ∀ A,eval p A=f (coset b v A) := by
  obtain ⟨q,hq,rep⟩ := hf
  obtain ⟨p,hp,h⟩ := explicit_pullback q hq b (fun j i => v i j)
  refine ⟨p,hp,fun A => ?_⟩
  rw [h,←rep]
  apply congrArg (eval q)
  ext j
  simp [support,coset,Finset.sum_apply]

private theorem local_unique (i : I) (p q : Coeff I)
    (agree : ∀ A,i∉A → eval p A=eval q A) :
    ∀ U,i∉U → p U=q U := by
  classical
  intro U
  induction U using Finset.strongInduction with
  | H U ih =>
    intro absent
    let c := fun T => p T-q T
    have zero : eval c U=0 := by
      unfold eval c
      rw [Finset.sum_sub_distrib,sub_eq_zero]
      exact agree U absent
    have only : eval c U=c U := by
      unfold eval
      apply Finset.sum_eq_single U
      · intro T hT ne
        have sub := Finset.mem_powerset.mp hT
        apply sub_eq_zero.mpr
        exact ih T (Finset.ssubset_iff_subset_ne.mpr ⟨sub,ne⟩) (fun h => absent (sub h))
      · simp
    exact sub_eq_zero.mp (only.symm.trans zero)

private theorem chart_step (b : Vec J) (v : I→Vec J) {A : Finset I} {i : I} (hi : i∉A) :
    coset b v (insert i A) = coset b v A+v i := by
  simp [coset,Finset.sum_insert,hi,add_comm,add_left_comm,add_assoc]

private theorem restrict_step (p : Coeff I) (i : I) (A : Finset I) (hi : i∉A) :
    eval (fun T => p (insert i T)) A=eval p (insert i A)+eval p A := by
  unfold eval
  rw [Finset.sum_powerset_insert hi]
  generalize (∑ T∈A.powerset,p T)=s
  generalize (∑ T∈A.powerset,p (insert i T))=t
  calc
    t = 0+t := (zero_add _).symm
    _ = (s+s)+t := by rw [CharTwo.add_self_eq_zero]
    _ = s+t+s := by ac_rfl

/-- A degree certificate for each directional difference gives a degree bound on every
coset chart. The chart directions may repeat and need not be linearly independent. -/
theorem positive (b : Vec J) (v : I→Vec J) (c : Coeff J) (d : ℕ)
    (der : ∀ i,HasDegree (derivative (fun x => eval c (support x)) (v i)) d) :
    ∃ p : Coeff I,degreeLE (d+1) p ∧ ∀ A,eval p A=eval c (support (coset b v A)) := by
  classical
  let f := fun x : Vec J => eval c (support x)
  have ambient : HasDegree f (Fintype.card J) :=
    ⟨c,fun S large => False.elim (large.not_ge (Finset.card_le_univ S)),fun _ => rfl⟩
  obtain ⟨p,_,rep⟩ := pull b v ambient
  refine ⟨p,?_,rep⟩
  intro S large
  obtain ⟨i,hi⟩ := Finset.card_pos.mp (show 0<S.card by omega)
  obtain ⟨q,small,eq⟩ := pull b v (der i)
  have agree (A : Finset I) (absent : i∉A) : eval (fun T => p (insert i T)) A=eval q A := by
    rw [restrict_step p i A absent,rep,rep,eq,chart_step b v absent]
    rfl
  have recover := local_unique i _ q agree (S.erase i) (Finset.notMem_erase i S)
  rw [Finset.insert_erase hi] at recover
  rw [recover]
  apply small
  rw [Finset.card_erase_of_mem hi]
  omega

/-- At degree zero the certificate requires genuine periods throughout the ambient space. -/
theorem period (b : Vec J) (v : I→Vec J) (c : Coeff J)
    (per : ∀ i x,derivative (fun z => eval c (support z)) (v i) x=0) :
    ∃ p : Coeff I,degreeLE 0 p ∧ ∀ A,eval p A=eval c (support (coset b v A)) := by
  classical
  let f := fun x : Vec J => eval c (support x)
  let p : Coeff I := fun T => if T=∅ then f b else 0
  have stable (A : Finset I) : f (coset b v A)=f b := by
    induction A using Finset.induction_on with
    | empty => simp [coset]
    | @insert i A absent ih =>
      rw [chart_step b v absent]
      have h := per i (coset b v A)
      change f (coset b v A+v i)+f (coset b v A)=0 at h
      have same := congrArg (fun z : F => z+f (coset b v A)) h
      simpa only [add_assoc,CharTwo.add_self_eq_zero,add_zero,zero_add,ih] using same
  refine ⟨p,?_,?_⟩
  · intro T pos
    have ne : T≠∅ := by rintro rfl; simp at pos
    simp [p,ne]
  · intro A
    change eval p A=f (coset b v A)
    simp [p,eval,stable]

#print axioms positive
#print axioms period
end ExactPlaneCosetDegree
