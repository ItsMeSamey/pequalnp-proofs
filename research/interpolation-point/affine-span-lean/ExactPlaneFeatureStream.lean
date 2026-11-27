import ExactPlaneGaussianMaterialized
import ExactPlanePivotCount
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas
import Mathlib.Data.List.Nodup

namespace ExactPlaneFeatureStream
open ExactPlaneGaussianMaterialized
open Submodule
abbrev F := ZMod 2
abbrev State (w : ℕ) (P : Type*) := Bank w 0 × List P
variable {w : ℕ} {P : Type*}

def row (vec : P→Vector F w) (x : P) : Row w 0 :=
  (vec x,Vector.replicate 0 0)

def features (vec : P→Vector F w) (x : P) : Fin w→F := fun j => (vec x)[j]

/-- Update with one payload. The source payload is retained exactly at a new pivot.
The eager elimination bank has zero provenance coordinates. -/
def step (vec : P→Vector F w) (st : State w P) (x : P) : State w P :=
  let t := reduce st.1 (row vec x)
  match ExactPlaneGaussian.pivot (readRow t).1 with
  | none => st
  | some i => (st.1++[(i,t)],x::st.2)

def select (vec : P→Vector F w) (xs : List P) : List P :=
  (xs.foldl (step vec) ([],[])).2.reverse

private theorem step_bank (v : P→Vector F w) (s : State w P) (x : P) :
    (step v s x).1=ExactPlaneGaussianMaterialized.insert s.1 (row v x) := by
  simp only [step,ExactPlaneGaussianMaterialized.insert]
  cases ExactPlaneGaussian.pivot (readRow (reduce s.1 (row v x))).1 <;> rfl

private theorem pivot_none (v : Fin w → F) :
    ExactPlaneGaussian.pivot v=none ↔ v=0 := by
  unfold ExactPlaneGaussian.pivot
  rw [List.find?_eq_none]
  constructor
  · intro h
    funext i
    simpa using h i (by simp)
  · rintro rfl
    simp

private theorem ker_test (s : ExactPlaneGaussian.Bank w (Fin 0))
    (r : ExactPlaneGaussian.Row w (Fin 0)) :
    (ExactPlaneGaussian.reduce s r).1=0 ↔ r.1∈ExactPlaneGaussian.represented s := by
  induction s generalizing r with
  | nil => rfl
  | cons a s ih => exact ih (ExactPlaneGaussian.clear a.1 a.2 r)

private theorem fresh_test (v : P→Vector F w) (s : Bank w 0) (x : P) :
    ExactPlaneGaussian.pivot (readRow (reduce s (row v x))).1=none ↔
      features v x∈ExactPlaneGaussian.represented (readBank s) := by
  rw [pivot_none,read_reduce,ker_test]
  rfl

def sites (xs : List P) : Set P := {x | x∈xs}
private theorem sites_cons (x : P) (xs : List P) : sites (x::xs)=insert x (sites xs) := by
  ext y; simp [sites]
private theorem sites_reverse (xs : List P) : sites xs.reverse=sites xs := by
  ext y; simp [sites]

private def back (v : P→Vector F w) (xs : List P) : State w P :=
  xs.foldr (fun x st => step v st x) ([],[])

private theorem back_spec (v : P→Vector F w) (xs : List P) :
    let st := back v xs
    (st.2.Sublist xs) ∧ st.2.Nodup ∧ LinearIndepOn F (features v) (sites st.2) ∧
    span F (features v '' sites st.2)=span F (features v '' sites xs) ∧
    ExactPlaneGaussian.represented (readBank st.1)=span F (features v '' sites xs) ∧
    ExactPlaneGaussian.Echelon (readBank st.1) ∧ st.1.length=st.2.length := by
  classical
  induction xs with
  | nil =>
    simp [back,sites,readBank,ExactPlaneGaussian.represented]
    constructor
    · change (LinearMap.id : (Fin w → F) →ₗ[F] (Fin w → F)).ker=⊥
      exact LinearMap.ker_id
    · exact ExactPlaneGaussian.Echelon.nil
  | cons x xs ih =>
    let s := back v xs
    obtain ⟨sub,nd,ind,eq,rep,ech,len⟩ := ih
    change (s.2.Sublist xs) at sub
    change s.2.Nodup at nd
    change LinearIndepOn F (features v) (sites s.2) at ind
    change span F (features v '' sites s.2)=_ at eq
    change ExactPlaneGaussian.represented (readBank s.1)=_ at rep
    change ExactPlaneGaussian.Echelon (readBank s.1) at ech
    change s.1.length=s.2.length at len
    change (step v s x).2.Sublist (x::xs) ∧ (step v s x).2.Nodup ∧
      LinearIndepOn F (features v) (sites (step v s x).2) ∧
      span F (features v '' sites (step v s x).2)=span F (features v '' sites (x::xs)) ∧
      ExactPlaneGaussian.represented (readBank (step v s x).1)=span F (features v '' sites (x::xs)) ∧
      ExactPlaneGaussian.Echelon (readBank (step v s x).1) ∧ (step v s x).1.length=(step v s x).2.length
    have bank := step_bank v s x
    have eche : ExactPlaneGaussian.Echelon (readBank (step v s x).1) := by
      rw [bank,read_insert]
      exact ExactPlaneGaussian.insert_echelon ech _
    have full : ExactPlaneGaussian.represented (readBank (step v s x).1)=
        span F (features v '' sites (x::xs)) := by
      rw [bank,read_insert,ExactPlaneGaussian.insert_span,rep,sites_cons,Set.image_insert_eq,
        Submodule.span_insert,sup_comm]
      rfl
    let t := reduce s.1 (row v x)
    cases e : ExactPlaneGaussian.pivot (readRow t).1 with
    | none =>
      have st : step v s x=s := by simp only [step]; exact (by rw [show reduce s.1 (row v x)=t from rfl,e])
      have dep := (fresh_test v s.1 x).mp e
      rw [rep] at dep
      refine ⟨by simpa only [st] using sub.cons x,by simpa only [st] using nd,
        by simpa only [st] using ind,?_,full,eche,by simpa only [st] using len⟩
      rw [st,eq,sites_cons,Set.image_insert_eq,Submodule.span_insert_eq_span dep]
    | some i =>
      have st : step v s x=(s.1++[(i,t)],x::s.2) := by
        simp only [step]; rw [show reduce s.1 (row v x)=t from rfl,e]
      have missing : features v x ∉ span F (features v '' sites xs) := by
        intro mem
        rw [←rep] at mem
        have none := (fresh_test v s.1 x).mpr mem
        rw [show reduce s.1 (row v x)=t from rfl,e] at none
        contradiction
      have fresh : features v x ∉ span F (features v '' sites s.2) := fun hm => missing (eq ▸ hm)
      have outside : x∉s.2 := fun mem => fresh (Submodule.subset_span ⟨x,mem,rfl⟩)
      refine ⟨by simpa only [st] using sub.cons_cons x,by simpa only [st] using
        (List.nodup_cons.mpr ⟨outside,nd⟩),?_,?_,full,eche,?_⟩
      · rw [st]; change LinearIndepOn F (features v) (sites (x::s.2))
        rw [sites_cons]; exact ind.insert fresh
      · rw [st]; change span F (features v '' sites (x::s.2))=_
        simp only [sites_cons,Set.image_insert_eq,Submodule.span_insert,eq]
      · rw [st]; simp [len]

theorem select_spec (v : P→Vector F w) (xs : List P) :
    (select v xs).Sublist xs ∧ (select v xs).Nodup ∧
      LinearIndepOn F (features v) (sites (select v xs)) ∧
      span F (features v '' sites (select v xs))=span F (features v '' sites xs) ∧
      (select v xs).length≤w := by
  obtain ⟨sub,nd,ind,eq,_,ech,len⟩ := back_spec v xs.reverse
  have sel : select v xs=(back v xs.reverse).2.reverse := by
    simp [select,back,List.foldr_reverse,Function.flip_def]
  rw [sel]
  have bound := ExactPlaneGaussian.bank_length_le ech
  rw [sites_reverse] at eq
  rw [sites_reverse]
  refine ⟨?_,by simpa using nd,ind,eq,?_⟩
  · simpa using sub.reverse
  · simpa [readBank,len] using bound

theorem positions (v : P→Vector F w) (xs : List P) :
    LinearIndependent F (fun j : Fin (select v xs).length => features v ((select v xs).get j)) := by
  obtain ⟨_,nd,ind,_,_⟩ := select_spec v xs
  let embed (j : Fin (select v xs).length) : ↥(sites (select v xs)) :=
    ⟨(select v xs).get j,List.get_mem ..⟩
  exact ind.comp embed (fun i j h => nd.injective_get (congrArg Subtype.val h))

#print axioms select_spec
#print axioms positions
end ExactPlaneFeatureStream
