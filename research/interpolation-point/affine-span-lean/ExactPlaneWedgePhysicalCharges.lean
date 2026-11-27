import ExactPlaneWedgeTotalCandidates
import ExactPlaneWedgeCodeCharges
import ExactPlaneWedgeRun
namespace ExactPlaneWedgePhysicalCharges
open ExactPlaneWedgePlan ExactPlaneWedgeRun ExactPlaneWedgeCodec ExactPlaneFeatureStream
open ExactPlaneWedgeArrayDP ExactPlaneWedgeTreeCharges ExactPlaneWedgeTotalCandidates
variable {n d : Nat}

def Width (w : Nat) : Indexed d n→Prop
  | .leaf _ c => c.rank≤w
  | .join l r c => Width w l ∧ Width w r ∧ c.rank≤w

theorem state_cap (w : Nat) (rows : LeafRows d n) (t : Indexed d n) (hw : Width w t) :
    Fits (2^(4*w)) (plan rows t) := by
  have bound (c : Cut d) (h : c.rank≤w) : size c ≤ 2^(4*w) := by
    unfold size
    rw [ExactPlaneWedgeCodeCharges.length_codes]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  induction t with
  | leaf i c => exact bound c hw
  | join l r c hl hr => exact ⟨hl hw.1,hr hw.2.1,bound c hw.2.2⟩

theorem leaf_bound (k : Fin n→Word d) (b : Fin n→ExactPlaneResidualPivots.Plane) (t : Indexed d n) :
    leafCap 4 (plan (inputs k b) t) := by
  induction t with
  | join l r c hl hr => exact ⟨hl,hr⟩
  | leaf i c =>
    intro j
    simp only [inputs, ExactPlaneWedgeLeaf.leaf,List.flatMap_cons,List.flatMap_nil,List.nil_append,
      List.append_nil,List.length_append]
    split <;> split <;> split <;> split <;> simp

theorem physical_cap (k : Fin n→Word d) (b : Fin n→ExactPlaneResidualPivots.Plane)
    (t : Indexed d n) (w : Nat) (width : Width w t) :
    let p := plan (inputs k b) t
    let D := 1+2*n+n.choose 2
    candidates selectFeatures p ≤ tips p*(2^(4*w)*4)+joins p*(2^(12*w)*(D*D)) := by
  let p := plan (inputs k b) t
  let D := 1+2*n+n.choose 2
  have fit := state_cap w (inputs k b) t width
  have cc := total_cap selectFeatures D (2^(4*w)) 4 (fun xs=>(selectFeatures_spec xs).2.2.2.2) p fit (leaf_bound k b t)
  have chk := checks_cap _ p fit
  have e : (2^(4*w):Nat)*(2^(4*w)*2^(4*w))=2^(12*w) := by rw [←pow_add,←pow_add]; congr 1; omega
  rw [e] at chk
  exact cc.trans (Nat.add_le_add_left (by simpa only [Nat.mul_assoc] using Nat.mul_le_mul_right (D*D) chk) _)

#print axioms physical_cap
end ExactPlaneWedgePhysicalCharges
