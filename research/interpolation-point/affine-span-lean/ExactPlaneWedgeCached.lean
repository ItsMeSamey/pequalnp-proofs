import ExactPlaneWedgeRawTree
namespace ExactPlaneWedgeRun
open ExactPlaneWedgeProduct ExactPlaneWedgeCodec ExactPlaneWedgeTree ExactPlaneWedgeDecorate
open ExactPlaneWedgeDecision ExactPlaneResidualPivots
open ExactPlanePhysicalConverse (ExactTrace)
open ExactPlaneWedgePlan ExactPlaneWedgeArrayDP
open ExactPlaneFeatureStream (selectFeatures)
variable {d n : Nat}

def cache (x : Feature n) : Feature n :=
  let a := Vector.ofFn x.2.1
  let b := Vector.ofFn x.2.2.1
  let m := Vector.ofFn fun i : Fin n => Vector.ofFn fun j : Fin n =>
    if h : i < j then x.2.2.2 ⟨(i,j),h⟩ else 0
  (x.1,fun i=>a[i],fun j=>b[j],fun p=>m[p.val.1][p.val.2])

@[simp] theorem cache_same (x : Feature n) : cache x=x := by
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ ?_))
  · rfl
  · funext i; simp [cache]
  · funext i; simp [cache]
  · funext i; simp [cache,i.property]

theorem cache_cells (n : Nat) :
    1+2*n+n*n ≤ 2*(1+2*n+n.choose 2) := by
  induction n with
  | zero => decide
  | succ n ih =>
    have expand : (n+1).choose 2=n.choose 1+n.choose 2 := Nat.choose_succ_succ _ _
    rw [expand,Nat.choose_one_right]
    nlinarith

def compress (xs : Rows n) : Rows n := (selectFeatures xs).map cache
theorem compress_eq : @compress n=selectFeatures := by
  funext xs
  have same : @cache n=id := funext cache_same
  simp [compress,same]

def cached (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane) : Option (Sites n × Sites n) :=
  let T := decorate k t ∅
  find h ((run compress (plan (inputs k b) T))[first (cut T)])

theorem cached_eq (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane) :
    cached t k b h=raw t k b h := by rw [cached,compress_eq]; rfl

theorem cached_spec (t : Tree n) (k : Fin n→Word d) (b h : Fin n→Plane)
    (sep : separated t) (cover : leaves t=Finset.univ) :
    (∀ uv,cached t k b h=some uv → Good k b h uv.1 uv.2 ∧ ExactTrace k b h (uv.1∪uv.2)) ∧
    (cached t k b h≠none ↔ ∃ A,ExactTrace k b h A) := by
  rw [cached_eq]
  exact raw_spec t k b h sep cover
#print axioms cached_spec
end ExactPlaneWedgeRun
