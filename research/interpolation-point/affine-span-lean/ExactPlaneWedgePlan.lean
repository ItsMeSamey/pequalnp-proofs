import ExactPlaneWedgeArrayDP
import ExactPlaneWedgeCodec
namespace ExactPlaneWedgePlan
open ExactPlaneWedgeArrayDP ExactPlaneWedgeCodec ExactPlaneWedgeTree
open ExactPlaneWedgeProduct (Feature F)
structure Cut (d : Nat) where
  rank : Nat
  columns : Fin rank → Word d
inductive Indexed (d n : Nat) where
  | leaf (i : Fin n) (cut : Cut d)
  | join (l r : Indexed d n) (cut : Cut d)
def cut : Indexed d n → Cut d
  | .leaf _ c | .join _ _ c => c
def tree : Indexed d n → Tree n
  | .leaf i _ => .leaf i
  | .join l r _ => .join (tree l) (tree r)
def size (c : Cut d) := (codes c.rank).length
def stateVector (c : Cut d) : Vector (Code c.rank) (size c) := ⟨(codes c.rank).toArray,by simp [size]⟩
abbrev LeafRows (d n : Nat) := (i : Fin n)→(c : Cut d)→Code c.rank→Rows n

def plan (rows : LeafRows d n) : (t : Indexed d n)→Plan n (size (cut t))
  | .leaf i c =>
    let v := stateVector c
    .leaf _ fun j => rows i c v[j]
  | .join l r c =>
    let left := plan rows l
    let right := plan rows r
    let va := stateVector (cut l)
    let vb := stateVector (cut r)
    let vc := stateVector c
    .join left right _ fun k i j => compatible (cut l).columns (cut r).columns c.columns va[i] vb[j] vc[k]

theorem has_code (c : Cut d) (x : Code c.rank) :
    ∃ i : Fin (size c), (stateVector c)[i]=x := by
  obtain ⟨i,e⟩ := List.mem_iff_get.mp (codes_complete x)
  refine ⟨i,?_⟩
  change (codes c.rank).toArray[i.val] = x
  simpa [List.get_eq_getElem] using e
end ExactPlaneWedgePlan
