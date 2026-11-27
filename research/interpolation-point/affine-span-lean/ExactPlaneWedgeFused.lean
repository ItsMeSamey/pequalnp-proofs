import ExactPlaneWedgeCached
import ExactPlaneFeaturePrefix
import ExactPlaneWedgeStore
namespace ExactPlaneWedgeFused
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgePlan ExactPlaneWedgeArrayDP
open ExactPlaneWedgeDecision ExactPlaneWedgeTree ExactPlaneWedgeDecorate ExactPlaneWedgeRun
open ExactPlaneFeatureStream (State step select select_spec prefixState prefix_bank_bound)
open ExactPlaneWedgeLayout (store dim makeLayout storeWith storeWith_eq)
open ExactPlaneResidualPivots
open ExactPlanePhysicalConverse (ExactTrace)
variable {n d l r m : Nat}

abbrev Acc (n : Nat) := State (dim n) (Feature n)
abbrev Encoder (n : Nat) := Feature n → Vector (ZMod 2) (dim n)
def push (enc : Encoder n) (st : Acc n) (a b : Feature n) : Acc n := step enc st (multiply a b)

def feed (enc : Encoder n) (ok : Fin l→Fin r→Bool) (L : Vector (Rows n) l) (R : Vector (Rows n) r)
    (s : Acc n) : Acc n :=
  (List.finRange l).foldl (fun state i =>
    (List.finRange r).foldl (fun state j =>
      if ok i j then
        L[i].foldl (fun state a => R[j].foldl (fun state b => push enc state a b) state) state
      else state) state) s

theorem feed_eq (enc : Encoder n) (ok : Fin l→Fin r→Bool) (L : Vector (Rows n) l) (R : Vector (Rows n) r)
    (s : Acc n) :
    feed enc ok L R s=(joined ok L R).foldl (step enc) s := by
  unfold feed joined
  simp only [List.foldl_flatMap]
  congr 1
  funext state i
  congr 1
  funext state j
  cases h : ok i j <;> simp [h,products,List.foldl_flatMap,List.foldl_map,push]

def finish (s : Acc n) : Rows n := s.2.reverse.map cache

def evaluate (enc : Encoder n) : {m : Nat} → Plan n m → Vector (Rows n) m
  | _,.leaf _ rows => Vector.ofFn fun i=>finish ((rows i).foldl (step enc) ([],[]))
  | _,.join a b _ ok =>
    let L := evaluate enc a
    let R := evaluate enc b
    Vector.ofFn fun i => finish (feed enc (ok i) L R ([],[]))

theorem evaluate_eq (p : Plan n m) : evaluate (store n) p=ExactPlaneWedgeArrayDP.run compress p := by
  induction p with
  | leaf => rfl
  | join a b m ok ia ib =>
    simp only [evaluate,ExactPlaneWedgeArrayDP.run,ia,ib]
    congr 1
    funext i
    rw [feed_eq]
    rfl

theorem prefix_bound (xs : List (Feature n)) :
    (prefixState (store n) xs).1.length≤dim n ∧
    (prefixState (store n) xs).2.length≤dim n := by
  refine ⟨prefix_bank_bound _ _,?_⟩
  have h := (select_spec (store n) xs).2.2.2.2
  simpa [select,prefixState] using h

theorem every_join_prefix (ok : Fin l→Fin r→Bool) (L : Vector (Rows n) l)
    (R : Vector (Rows n) r) (j : Nat) :
    let st := prefixState (store n) ((joined ok L R).take j)
    st.1.length≤dim n ∧ st.2.length≤dim n := prefix_bound _

def solve (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane) : Option (Sites n × Sites n) :=
  let T := decorate k t ∅
  let lookup := makeLayout n
  let enc := storeWith lookup
  find h ((evaluate enc (plan (inputs k b) T))[first (cut T)])

theorem solve_eq (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane) :
    solve t k b h=cached t k b h := by simp only [solve,cached,storeWith_eq,evaluate_eq]
theorem solve_spec (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane)
    (sep : separated t) (cover : leaves t=Finset.univ) :
    (∀ uv,solve t k b h=some uv → Good k b h uv.1 uv.2 ∧ ExactTrace k b h (uv.1∪uv.2)) ∧
    (solve t k b h≠none ↔ ∃ A,ExactTrace k b h A) := by
  rw [solve_eq]
  exact cached_spec t k b h sep cover
#print axioms feed_eq
#print axioms prefix_bound
#print axioms solve_spec
end ExactPlaneWedgeFused
