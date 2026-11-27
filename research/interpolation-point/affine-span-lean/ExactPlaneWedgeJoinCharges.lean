import Mathlib.Data.List.Basic
import Mathlib.Algebra.BigOperators.Group.List.Basic

namespace ExactPlaneWedgeJoinCharges
variable {P L R A B : Type*}

-- Counts accepted Cartesian products even when the resulting rows coincide.
def perRight (ok : P → L → R → Bool) (p : P) (l : L) (a : List A) (bs : R → List B)
    (rs : List R) : Nat :=
  (rs.map (fun r => if ok p l r then a.length * (bs r).length else 0)).sum

def perLeft (ok : P → L → R → Bool) (p : P) (as : L → List A) (bs : R → List B)
    (ls : List L) (rs : List R) : Nat :=
  (ls.map (fun l => perRight ok p l (as l) bs rs)).sum

def products (ok : P → L → R → Bool) (as : L → List A) (bs : R → List B)
    (ps : List P) (ls : List L) (rs : List R) : Nat :=
  (ps.map (fun p => perLeft ok p as bs ls rs)).sum

private theorem sum_cap (xs : List A) (v : A → Nat) (M : Nat)
    (h : ∀ x∈xs,v x≤M) : (xs.map v).sum ≤ xs.length*M := by
  induction xs with
  | nil => simp
  | cons a xs ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
    have rest : (xs.map v).sum ≤ xs.length*M := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have head : v a ≤ M := h a (List.mem_cons_self ..)
    simpa only [Nat.add_comm M (xs.length*M)] using Nat.add_le_add head rest

theorem product_cap (ok : P → L → R → Bool) (as : L → List A) (bs : R → List B)
    (ps : List P) (ls : List L) (rs : List R) (D : Nat)
    (ha : ∀ l∈ls,(as l).length≤D) (hb : ∀ r∈rs,(bs r).length≤D) :
    products ok as bs ps ls rs ≤ ps.length * (ls.length * (rs.length * (D*D))) := by
  apply sum_cap
  intro p _
  apply sum_cap
  intro l hl
  apply sum_cap
  intro r hr
  split
  · exact Nat.mul_le_mul (ha l hl) (hb r hr)
  · exact Nat.zero_le _

theorem triple_cap (p l r w : Nat) (hp : p≤2^(4*w)) (hl : l≤2^(4*w)) (hr : r≤2^(4*w)) :
    p*(l*r)≤2^(12*w) := by
  calc
    _ ≤ 2^(4*w)*(2^(4*w)*2^(4*w)) := Nat.mul_le_mul hp (Nat.mul_le_mul hl hr)
    _ = _ := by rw [←pow_add,←pow_add]; congr 1; omega

#print axioms product_cap
#print axioms triple_cap
end ExactPlaneWedgeJoinCharges
