import ExactPlaneWedgeArrayDP
import ExactPlaneWedgeJoinCharges
namespace ExactPlaneWedgeArrayCharges
open ExactPlaneWedgeArrayDP
variable {n l r : Nat}

theorem lengths (xs ys : Rows n) :
    (products xs ys).length=xs.length*ys.length := by
  simp [products,List.length_flatMap,List.sum_replicate]

theorem real_count (ok : Fin l→Fin r→Bool) (a : Vector (Rows n) l) (b : Vector (Rows n) r) :
    (joined ok a b).length =
      ExactPlaneWedgeJoinCharges.perLeft (fun (_ : Unit) => ok) ()
      (fun i => a[i]) (fun j => b[j]) (List.finRange l) (List.finRange r) := by
  simp [joined,List.length_flatMap,ExactPlaneWedgeJoinCharges.perLeft,ExactPlaneWedgeJoinCharges.perRight,
    List.map_map,Function.comp_def,lengths,apply_ite]

theorem actual_cap (ok : Fin l→Fin r→Bool) (a : Vector (Rows n) l) (b : Vector (Rows n) r)
    (D : Nat) (ha : ∀i : Fin l,(a[i]).length≤D) (hb : ∀j : Fin r,(b[j]).length≤D) :
    (joined ok a b).length≤ l*(r*(D*D)) := by
  rw [real_count]
  have h := ExactPlaneWedgeJoinCharges.product_cap (fun (_ : Unit) => ok)
    (fun i => a[i]) (fun j => b[j]) [()] (List.finRange l) (List.finRange r) D
    (fun i _=>ha i) (fun j _=>hb j)
  simpa [ExactPlaneWedgeJoinCharges.products] using h
#print axioms actual_cap
end ExactPlaneWedgeArrayCharges
