import ThreeNameSplitCircuit
import Mathlib.Data.Finset.SDiff
namespace ThreeNameChain
open scoped BigOperators
open ThreeNameSplitCircuit
variable {ι V : Type*} [DecidableEq ι] [AddCommGroup V]

structure Carrier (ι V : Type*) where
  ground : Finset ι
  col : ι → V

def Rooted (p : Carrier ι V) (R : Finset ι) :=
  ∃ C ⊆ p.ground, R ⊆ C ∧ Circuit p.col C

/-- Fresh interface labels are in a common abstract label space. For a pair
of shore subsets with equal nonzero sums, full completion supplies one label. -/
structure Step (R : Finset ι) (p q : Carrier ι V) where
  retained : Finset ι
  roots : R ⊆ retained
  keep : retained ⊆ q.ground
  same : ∀ i ∈ retained, q.col i = p.col i
  complete : ∀ A ⊆ retained, ∀ B ⊆ p.ground \ retained,
    (∑ i ∈ A, p.col i) ≠ 0 → (∑ i ∈ A, p.col i) = ∑ i ∈ B, p.col i →
      ∃ f ∈ q.ground, f ∉ p.ground ∧ q.col f = ∑ i ∈ A, p.col i

theorem forward {p q : Carrier ι V} {R : Finset ι} (rn : R.Nonempty)
    (binary : ∀ x : V, x+x=0) (s : Step R p q) (hp : Rooted p R) : Rooted q R := by
  classical
  obtain ⟨C,hC,hR,hc⟩ := hp
  by_cases hit : C ⊆ s.retained
  · exact ⟨C,hit.trans s.keep,hR,contained hc (fun i hi => s.same i (hit hi))⟩
  · let A := C ∩ s.retained
    let B := C \ s.retained
    have hA : A ⊆ s.retained := Finset.inter_subset_right
    have hB : B ⊆ p.ground \ s.retained := fun i hi =>
      Finset.mem_sdiff.mpr ⟨hC (Finset.mem_sdiff.mp hi).1,(Finset.mem_sdiff.mp hi).2⟩
    have hr : R ⊆ A := fun i hi => Finset.mem_inter.mpr ⟨hR hi,s.roots hi⟩
    have ha : A.Nonempty := rn.mono hr
    have hb : B.Nonempty := by
      by_contra h
      apply hit
      intro i hi
      by_contra absent
      exact h ⟨i,Finset.mem_sdiff.mpr ⟨hi,absent⟩⟩
    have dj : Disjoint A B := Finset.disjoint_left.mpr (fun i hi hj =>
      (Finset.mem_sdiff.mp hj).2 ((Finset.mem_inter.mp hi).2))
    have union : A ∪ B = C := by
      rw [Finset.union_comm]
      exact Finset.sdiff_union_inter _ _
    have hc' : Circuit p.col (A ∪ B) := union.symm ▸ hc
    have eqsum : (∑ i ∈ A, p.col i) + (∑ i ∈ B, p.col i) = 0 := by
      rw [← Finset.sum_union dj]
      exact hc'.2.1
    have eq : (∑ i ∈ A, p.col i) = ∑ i ∈ B, p.col i :=
      add_left_cancel ((binary _).trans eqsum.symm)
    have nz : (∑ i ∈ A, p.col i) ≠ 0 := by
      intro hz
      have hh := hc'.2.2 A Finset.subset_union_left ha hz
      obtain ⟨b,bm⟩ := hb
      exact Finset.disjoint_left.mp dj (hh.symm ▸ Finset.mem_union_right A bm) bm
    obtain ⟨f,fq,fp,fv⟩ := s.complete A hA B hB nz eq
    have fresh : f ∉ A ∪ B := fun h => fp (hC (union ▸ h))
    obtain ⟨_,_,_,child,root⟩ := crossing binary dj ha hb fresh hr hc'
    refine ⟨insert f A,Finset.insert_subset fq (hA.trans s.keep),root,contained child ?_⟩
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | mem
    · simpa using fv
    · have ne : i ≠ f := fun e => fresh (e ▸ Finset.mem_union_left B mem)
      simpa [ne] using s.same i (hA mem)

inductive Path (R : Finset ι) : Carrier ι V → Carrier ι V → Prop
  | nil (p) : Path R p p
  | cons {p q t} (head : Step R p q) (tail : Path R q t) : Path R p t

theorem rejects {p q : Carrier ι V} {R : Finset ι} (rn : R.Nonempty)
    (binary : ∀ x : V, x+x=0) (path : Path R p q) (last : ¬Rooted q R) : ¬Rooted p R := by
  induction path with
  | nil => exact last
  | cons head tail ih => exact fun h => ih last (forward rn binary head h)

#print axioms rejects
#print axioms forward
end ThreeNameChain
