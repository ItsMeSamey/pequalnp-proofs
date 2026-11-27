import Lean

namespace ReadOnceP4

/-- A possible final gate of a positive read-once formula. Its two
children receive disjoint subsets of the four varying leaves. -/
def rootValue (useAnd a b c d : Bool) (f g : Bool → Bool → Bool → Bool → Bool)
    (x y z w : Bool) : Bool :=
  let l := f (a && x) (b && y) (c && z) (d && w)
  let r := g (!a && x) (!b && y) (!c && z) (!d && w)
  if useAnd then l && r else l || r

/-- A connected three-edge bipartite path, with its missing corner
rejected, cannot have a nontrivial read-once root split. The child
functions may be arbitrary apart from vanishing on the zero vector. -/
theorem no_split (op a b c d : Bool) (f g : Bool → Bool → Bool → Bool → Bool)
    (leftUsed : a || b || c || d = true)
    (rightUsed : !a || !b || !c || !d = true)
    (fzero : f false false false false = false)
    (gzero : g false false false false = false)
    (sx : rootValue op a b c d f g true false false false = false)
    (sy : rootValue op a b c d f g false true false false = false)
    (sz : rootValue op a b c d f g false false true false = false)
    (sw : rootValue op a b c d f g false false false true = false)
    (xz : rootValue op a b c d f g true false true false = true)
    (xw : rootValue op a b c d f g true false false true = true)
    (yz : rootValue op a b c d f g false true true false = true)
    (yw : rootValue op a b c d f g false true false true = false) : False := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [rootValue] <;> grind

end ReadOnceP4
