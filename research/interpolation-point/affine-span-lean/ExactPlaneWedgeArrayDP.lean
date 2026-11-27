import ExactPlaneWedgeTree
namespace ExactPlaneWedgeArrayDP
open ExactPlaneWedgeProduct ExactPlaneWedgeTree Submodule
variable {n : Nat}
abbrev Rows (n : Nat) := List (Feature n)
def items (xs : Rows n) : Set (Feature n) := {x | x∈xs}

inductive Plan (n : Nat) : Nat → Type where
  | leaf (m : Nat) (rows : Fin m→Rows n) : Plan n m
  | join {l r : Nat} (left : Plan n l) (right : Plan n r) (m : Nat)
      (ok : Fin m→Fin l→Fin r→Bool) : Plan n m

def products (xs ys : Rows n) : Rows n :=
  xs.flatMap fun a => ys.map fun b => multiply a b

def joined (ok : Fin l→Fin r→Bool) (left : Vector (Rows n) l) (right : Vector (Rows n) r) : Rows n :=
  (List.finRange l).flatMap fun i => (List.finRange r).flatMap fun j =>
    if ok i j then products left[i] right[j] else []

theorem joined_eq (ok : Fin l→Fin r→Bool) (left : Vector (Rows n) l) (right : Vector (Rows n) r) :
    items (joined ok left right) = combine (fun i j=>ok i j=true)
      (fun i=>items left[i]) (fun j=>items right[j]) := by
  ext z
  rw [mem_combine]
  change z∈joined ok left right ↔ _
  simp only [joined,List.mem_flatMap,List.mem_finRange,true_and]
  constructor
  · rintro ⟨i,j,h⟩
    cases eq : ok i j with
    | false => simp [eq] at h
    | true =>
      simp only [eq,ite_true,products,List.mem_flatMap,List.mem_map] at h
      obtain ⟨x,hx,y,hy,eq'⟩ := h
      exact ⟨i,j,eq,x,hx,y,hy,eq'⟩
  · rintro ⟨i,j,h,x,hx,y,hy,e⟩
    refine ⟨i,j,?_⟩
    simp only [h,ite_true,products,List.mem_flatMap,List.mem_map]
    exact ⟨x,hx,y,hy,e⟩

/-- Every child table is a strict vector bound once, before parent tabulation. -/
def run (compress : Rows n→Rows n) : {m : Nat} → Plan n m → Vector (Rows n) m
  | _,.leaf _ rows => Vector.ofFn fun i => compress (rows i)
  | _,.join left right _ ok =>
    let a := run compress left
    let b := run compress right
    Vector.ofFn fun i => compress (joined (ok i) a b)

def semantics : {m : Nat}→Plan n m→Fin m→Set (Feature n)
  | _,.leaf _ rows,i => items (rows i)
  | _,.join left right _ ok,i =>
    combine (fun j k=>ok i j k=true) (semantics left) (semantics right)

private theorem atOf {P : Type*} {k : Nat} (f : Fin k→P) (i : Fin k) :
    (Vector.ofFn f)[i] = f i := by
  change (Vector.ofFn f)[i.val] = _
  exact Vector.getElem_ofFn i.isLt

theorem exact (compress : Rows n→Rows n)
    (law : ∀ xs, items (compress xs)⊆items xs ∧
      span F (items (compress xs))=span F (items xs))
    {m : Nat} (p : Plan n m) (i : Fin m) :
    items (run compress p)[i]⊆semantics p i ∧
      span F (items (run compress p)[i])=span F (semantics p i) := by
  induction p with
  | leaf m rows =>
    simpa only [run,semantics,atOf] using law (rows i)
  | join left right m ok ihl ihr =>
    let a := run compress left
    let b := run compress right
    obtain ⟨sub,sp⟩ := law (joined (ok i) a b)
    simp only [run,semantics,atOf]
    refine ⟨?_,?_⟩
    · intro z hz
      have h := sub hz
      rw [joined_eq] at h
      obtain ⟨j,k,jk,x,hx,y,hy,eq⟩ := (mem_combine _ _ _ z).mp h
      exact (mem_combine _ _ _ _).mpr ⟨j,k,jk,x,(ihl j).1 hx,y,(ihr k).1 hy,eq⟩
    · rw [joined_eq] at sp
      exact sp.trans (combine_span _ _ _ _ _ (fun j=>(ihl j).2) (fun k=>(ihr k).2))

#print axioms exact
end ExactPlaneWedgeArrayDP
