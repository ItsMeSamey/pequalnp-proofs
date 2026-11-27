import ExactPlaneWedgeFused
import ExactPlaneWedgePhysicalCharges
namespace ExactPlaneWedgeFusedCharges
open ExactPlaneWedgeProduct ExactPlaneWedgeArrayDP ExactPlaneWedgeFused ExactPlaneWedgeRun
open ExactPlaneFeatureStream (step)
variable {n l r m : Nat}

def traversal {T : Type*} (f : T→Feature n→T) (ok : Fin l→Fin r→Bool)
    (L : Vector (Rows n) l) (R : Vector (Rows n) r) (s : T) : T :=
  (List.finRange l).foldl (fun state i =>
    (List.finRange r).foldl (fun state j => if ok i j then
      L[i].foldl (fun state a => R[j].foldl (fun state b => f state (multiply a b)) state) state
      else state) state) s

theorem erase_counter (enc : Encoder n) (ok : Fin l→Fin r→Bool)
    (L : Vector (Rows n) l) (R : Vector (Rows n) r) (s : Acc n) :
    traversal (step enc) ok L R s=feed enc ok L R s := rfl

theorem traversal_eq {T : Type*} (f : T→Feature n→T) (ok : Fin l→Fin r→Bool)
    (L : Vector (Rows n) l) (R : Vector (Rows n) r) (s : T) :
    traversal f ok L R s=(joined ok L R).foldl f s := by
  unfold traversal joined
  simp only [List.foldl_flatMap]
  congr 1
  funext state i
  congr 1
  funext state j
  cases h : ok i j <;> simp [h,products,List.foldl_flatMap,List.foldl_map]

theorem callbacks (ok : Fin l→Fin r→Bool) (L : Vector (Rows n) l) (R : Vector (Rows n) r) :
    traversal (fun count _=>count+1) ok L R 0=(joined ok L R).length := by
  rw [traversal_eq]
  have aux (xs : Rows n) (k : Nat) : xs.foldl (fun count _=>count+1) k=k+xs.length := by
    induction xs generalizing k with
    | nil => simp
    | cons a xs ih => simp only [List.foldl_cons,List.length_cons,ih]; omega
  simpa using aux (joined ok L R) 0

def calls (enc : Encoder n) : {m : Nat} → Plan n m → Nat
  | m,.leaf _ rows => ((List.finRange m).map (fun i=>(rows i).length)).sum
  | m,.join a b _ ok =>
    let L := evaluate enc a
    let R := evaluate enc b
    calls enc a+calls enc b+((List.finRange m).map
      (fun i=>traversal (fun count _=>count+1) (ok i) L R 0)).sum

theorem same_count (p : Plan n m) :
    calls (ExactPlaneWedgeLayout.store n) p =
    ExactPlaneWedgeTotalCandidates.candidates ExactPlaneFeatureStream.selectFeatures p := by
  induction p with
  | leaf => rfl
  | join a b m ok ha hb =>
    simp only [calls,ExactPlaneWedgeTotalCandidates.candidates,ha,hb,evaluate_eq,compress_eq,callbacks]

theorem fused_cap {d : Nat} (k : Fin n→ExactPlaneWedgeCodec.Word d)
    (b : Fin n→ExactPlaneResidualPivots.Plane) (t : ExactPlaneWedgePlan.Indexed d n) (w : Nat)
    (width : ExactPlaneWedgePhysicalCharges.Width w t) :
    let p := ExactPlaneWedgePlan.plan (inputs k b) t
    let D := 1+2*n+n.choose 2
    calls (ExactPlaneWedgeLayout.storeWith (ExactPlaneWedgeLayout.makeLayout n)) p ≤
      ExactPlaneWedgeTreeCharges.tips p*(2^(4*w)*4)+
      ExactPlaneWedgeTreeCharges.joins p*(2^(12*w)*(D*D)) := by
  simp only [ExactPlaneWedgeLayout.storeWith_eq,same_count]
  exact ExactPlaneWedgePhysicalCharges.physical_cap k b t w width

#print axioms fused_cap
end ExactPlaneWedgeFusedCharges
