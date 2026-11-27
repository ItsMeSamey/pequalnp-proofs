import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.Pi
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Data.Fintype.Basic

namespace ExactPlaneGaussian
open scoped BigOperators
abbrev F := ZMod 2
abbrev V (d : ℕ) := Fin d → F
abbrev Row (d : ℕ) (I : Type*) := V d × (I → F)
abbrev Bank (d : ℕ) (I : Type*) := List (Fin d × Row d I)
variable {d : ℕ} {I : Type*}

def clear (i : Fin d) (p r : Row d I) : Row d I := r + r.1 i • p

def reduce : Bank d I → Row d I → Row d I
  | [], r => r
  | (i,p)::tail, r => reduce tail (clear i p r)

def pivot (x : V d) := (List.finRange d).find? (fun i => decide (x i ≠ 0))

def insert (s : Bank d I) (r : Row d I) : Bank d I :=
  let p := reduce s r
  match pivot p.1 with
  | none => s
  | some i => s ++ [(i,p)]

def build [DecidableEq I] (v : I → V d) : List I → Bank d I
  | [] => []
  | i::l => insert (build v l) (v i,Pi.single i 1)

def solve [DecidableEq I] (A : List I) (v : I → V d) (y : V d) : Option (I → F) :=
  let r := reduce (build v A) (y,0)
  if r.1=0 then some r.2 else none

private theorem self_add {M : Type*} [AddCommGroup M] [Module F M] (x : M) : x+x=0 := by
  have h : (1:F)+1=0 := by decide
  calc
    x+x=((1:F)+1) • x := by simp [add_smul]
    _=0 := by rw [h,zero_smul]

private theorem pivot_none (x : V d) (h : pivot x=none) : x=0 := by
  unfold pivot at h
  rw [List.find?_eq_none] at h
  funext i
  simpa using h i (by simp)

private theorem pivot_one (x : V d) {i : Fin d} (h : pivot x=some i) : x i=1 := by
  unfold pivot at h
  have test : (fun j : Fin d => decide (x j≠0)) i = true := List.find?_some (p := fun j : Fin d => decide (x j≠0)) h
  have nz : x i ≠ 0 := of_decide_eq_true test
  have cls : ∀ a:F,a=0 ∨ a=1 := by decide
  exact (cls _).resolve_left nz

private def stepMap (i : Fin d) (p : V d) : V d →ₗ[F] V d :=
  LinearMap.id + (LinearMap.proj i).smulRight p

private def normal : Bank d I → V d →ₗ[F] V d
  | [] => LinearMap.id
  | (i,p)::s => (normal s).comp (stepMap i p.1)

private theorem reduce_val (s : Bank d I) (r : Row d I) :
    (reduce s r).1=normal s r.1 := by
  induction s generalizing r with
  | nil => rfl
  | cons a s ih => exact ih (clear a.1 a.2 r)

private theorem normal_append (s t : Bank d I) (v : V d) :
    normal (s++t) v = normal t (normal s v) := by
  induction s generalizing v with
  | nil => rfl
  | cons a s ih => exact ih (stepMap a.1 a.2.1 v)

def represented (s : Bank d I) : Submodule F (V d) := LinearMap.ker (normal s)

theorem insert_span (s : Bank d I) (r : Row d I) :
    represented (insert s r) = represented s ⊔ Submodule.span F {r.1} := by
  classical
  let p := reduce s r
  have val : p.1=normal s r.1 := reduce_val _ _
  change represented (match pivot p.1 with | none => s | some i => s++[(i,p)])=_
  cases e : pivot p.1 with
  | none =>
    simp only
    have mem : r.1 ∈ represented s := val.symm.trans (pivot_none _ e)
    exact (sup_eq_left.mpr (Submodule.span_le.mpr (by simpa using mem))).symm
  | some i =>
    simp only
    have one := pivot_one _ e
    let W := represented s ⊔ Submodule.span F {r.1}
    have memx : r.1∈W := (show Submodule.span F {r.1} ≤ W from le_sup_right)
      (Submodule.subset_span (Set.mem_singleton r.1))
    have test (x : V d) : x∈represented (s++[(i,p)]) ↔
        normal s x + (normal s x i) • p.1=0 := by
      change normal (s++[(i,p)]) x=0 ↔ _
      rw [normal_append]
      rfl
    apply le_antisymm
    · intro x hx
      let a := normal s x i
      have cancel : x+a • r.1 ∈ represented s := by
        change normal s (x+a • r.1)=0
        rw [map_add,map_smul,←val]
        exact (test x).mp hx
      have hw : x+a • r.1∈W := (show represented s≤W from le_sup_left) cancel
      have both := W.add_mem hw (W.smul_mem a memx)
      simpa only [add_assoc,self_add,add_zero] using both
    · apply sup_le
      · intro x hx
        apply (test x).mpr
        change normal s x=0 at hx
        simp [hx]
      · apply Submodule.span_le.mpr
        apply Set.singleton_subset_iff.mpr
        apply (test _).mpr
        rw [←val,one,one_smul,self_add]

theorem build_span [DecidableEq I] (v : I → V d) (A : List I) :
    represented (build v A) = Submodule.span F (v '' (A.toFinset : Set I)) := by
  induction A with
  | nil => simp [build,represented,normal]
  | cons i l ih =>
    rw [build,insert_span,ih]
    simp [Set.image_insert_eq,Submodule.span_insert,sup_comm]

theorem solve_hits [DecidableEq I] (A : List I) (v : I → V d) (y : V d) :
    (∃ mask,solve A v y=some mask) ↔ y ∈ Submodule.span F (v '' (A.toFinset : Set I)) := by
  rw [←build_span]
  change _ ↔ normal (build v A) y=0
  simp only [solve,reduce_val]
  split <;> simp_all

/-- Pivot order is the order of insertion. Later pivots vanish at every earlier pivot
coordinate. The coordinate labels need not be numerically increasing. -/
inductive Echelon : Bank d I → Prop
  | nil : Echelon []
  | snoc {s : Bank d I} {i : Fin d} {p : Row d I} : Echelon s → p.1 i=1 →
      (∀ a∈s,p.1 a.1=0) → Echelon (s++[(i,p)])

private theorem normal_zero_at {s : Bank d I} (hs : Echelon s) (x : V d) :
    ∀ a∈s,normal s x a.1=0 := by
  induction hs with
  | nil => simp
  | @snoc s i p _ one zeros ih =>
    intro a mem
    rw [normal_append]
    change normal s x a.1 + normal s x i * p.1 a.1=0
    rcases List.mem_append.mp mem with old|new
    · rw [ih a old,zeros a old,mul_zero,add_zero]
    · obtain rfl := List.mem_singleton.mp new
      simpa only [one,mul_one] using self_add (normal s x i)

theorem insert_echelon {s : Bank d I} (hs : Echelon s) (r : Row d I) : Echelon (insert s r) := by
  simp only [insert]
  split
  · exact hs
  · rename_i i eq
    apply Echelon.snoc hs (pivot_one _ eq)
    intro a ha
    rw [reduce_val]
    exact normal_zero_at hs _ a ha

theorem build_echelon [DecidableEq I] (v : I → V d) (A : List I) : Echelon (build v A) := by
  induction A with
  | nil => exact Echelon.nil
  | cons i l ih => exact insert_echelon ih _

private theorem reduce_preserves {s : Bank d I} (T : Submodule F (Row d I))
    (hs : ∀ a∈s,a.2∈T) (r : Row d I) (hr : r∈T) : reduce s r∈T := by
  induction s generalizing r with
  | nil => exact hr
  | cons a s ih =>
    exact ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)) _ (T.add_mem hr
      (T.smul_mem _ (hs a (List.mem_cons_self ..))))

private theorem insert_preserves {s : Bank d I} (T : Submodule F (Row d I))
    (hs : ∀ a∈s,a.2∈T) (r : Row d I) (hr : r∈T) : ∀ a∈insert s r,a.2∈T := by
  simp only [insert]
  split
  · exact hs
  · intro a ha
    rcases List.mem_append.mp ha with old|new
    · exact hs a old
    · obtain rfl := List.mem_singleton.mp new
      exact reduce_preserves T hs r hr

private theorem build_preserves [DecidableEq I] (v : I → V d) (A : List I)
    (T : Submodule F (Row d I)) (atoms : ∀ i∈A,(v i,Pi.single i (1:F))∈T) :
    ∀ a∈build v A,a.2∈T := by
  induction A with
  | nil => simp [build]
  | cons i l ih =>
    exact insert_preserves T
      (ih (fun j hj => atoms j (List.mem_cons_of_mem _ hj))) _
      (atoms i (List.mem_cons_self ..))

/-- The columns of the full original indexed matrix decode a returned coefficient mask. -/
def decode [Fintype I] (v : I → V d) : (I→F) →ₗ[F] V d :=
  ∑ i, (LinearMap.proj i).smulRight (v i)

private theorem decode_single [Fintype I] [DecidableEq I] (v : I → V d) (i : I) :
    decode v (Pi.single i 1)=v i := by
  classical
  simp [decode,LinearMap.sum_apply,Pi.single_apply]

private def discrepancy [Fintype I] (v : I → V d) : Row d I →ₗ[F] V d :=
  LinearMap.fst F _ _ - (decode v).comp (LinearMap.snd F _ _)

private theorem reduce_agrees {s : Bank d I} {M : Type*} [AddCommGroup M] [Module F M]
    (D : Row d I →ₗ[F] M) (hs : ∀ a∈s,D a.2=0) (r : Row d I) :
    D (reduce s r)=D r := by
  induction s generalizing r with
  | nil => rfl
  | cons a s ih =>
    change D (reduce s (clear a.1 a.2 r))=D r
    rw [ih (fun p hp => hs p (List.mem_cons_of_mem _ hp)),clear,map_add,map_smul,
      hs a (List.mem_cons_self ..),smul_zero,add_zero]

theorem solve_witness [Fintype I] [DecidableEq I] (A : List I) (v : I → V d)
    (y : V d) (mask : I→F) (ok : solve A v y=some mask) :
    decode v mask=y ∧ ∀ i∉A, mask i=0 := by
  let s := build v A
  let r := reduce s (y,0)
  change (if r.1=0 then some r.2 else none)=some mask at ok
  split at ok
  next hz =>
    have em : r.2=mask := Option.some.inj ok
    constructor
    · let D := discrepancy v
      have piv : ∀ a∈s,D a.2=0 := build_preserves v A (LinearMap.ker D)
        (fun i _ => by change v i-decode v (Pi.single i 1)=0; rw [decode_single,sub_self])
      have eq := reduce_agrees D piv (y,0)
      change r.1-decode v r.2 = y - decode v 0 at eq
      rw [hz,em,map_zero,sub_zero,zero_sub] at eq
      have neg : -(decode v mask)=decode v mask :=
        neg_eq_iff_add_eq_zero.mpr (self_add _)
      rwa [neg] at eq
    · intro i outside
      let D : Row d I →ₗ[F] F := (LinearMap.proj i).comp (LinearMap.snd F _ _)
      have piv : ∀ a∈s,D a.2=0 := build_preserves v A (LinearMap.ker D)
        (fun j hj => by
          have ne : i≠j := fun eq => outside (eq ▸ hj)
          change (Pi.single j (1:F) : I → F) i=0
          simp [Pi.single_apply,ne,Ne.symm ne])
      have eq := reduce_agrees D piv (y,0)
      change r.2 i=0 at eq
      rwa [em] at eq
  next => contradiction

#print axioms solve_hits
#print axioms build_echelon
#print axioms solve_witness
end ExactPlaneGaussian
