import ThresholdUniqueRaw
open PEqualNP.CircuitLowerBounds ResidualSurplus ThresholdOrGroups
namespace ThresholdFactorExpr
inductive Term where
  | raw (i : Nat)
  | ref (j : Nat)
  | node (op : Op) (l r : Term)
deriving DecidableEq

def Term.cost : Term → Nat
  | .raw _ | .ref _ => 0
  | .node _ l r => l.cost+r.cost+1

def Term.value (raw ref : Nat → Bool) : Term → Bool
  | .raw i => raw i
  | .ref i => ref i
  | .node o l r => act o (l.value raw ref) (r.value raw ref)

def Term.Avail (n : Nat) (seen : List Nat) : Term → Prop
  | .raw i => i<n
  | .ref i => i∈seen
  | .node _ l r => l.Avail n seen ∧ r.Avail n seen

def Term.build (ren : Nat → Nat) (k : Nat) : Term → List Gate × Nat
  | .raw i => ([],i)
  | .ref i => ([],ren i)
  | .node o l r =>
    let a := l.build ren k
    let b := r.build ren (k+a.1.length)
    (a.1 ++ b.1 ++ [binary o a.2 b.2],k+a.1.length+b.1.length)

private theorem append_run (gs hs : List Gate) (w : List Bool) :
    run (gs++hs) w=run hs (run gs w) := by simp [run,List.foldl_append]
private theorem length_run (gs : List Gate) (w : List Bool) :
    (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[val g w])).length=_
    rw [ih]; simp <;> omega
private theorem earlier (gs : List Gate) (w : List Bool) (i : Nat) (lt : i<w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false=_
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]

theorem term_build (t : Term) (n : Nat) (seen : List Nat) (ren : Nat → Nat) (w : List Bool)
    (av : t.Avail n seen) (nr : n≤w.length) (ext : ∀ j∈seen,ren j<w.length) :
    let a := t.build ren w.length
    a.1.length=t.cost ∧ Mono a.1 ∧ a.2<w.length+a.1.length ∧
    (run a.1 w).getD a.2 false=t.value (fun i => w.getD i false) (fun j => w.getD (ren j) false) := by
  induction t generalizing w with
  | raw i => exact ⟨rfl,by simp [Term.build,Mono],by change i<w.length+0; change i<n at av; omega,rfl⟩
  | ref j => exact ⟨rfl,by simp [Term.build,Mono],by simpa [Term.build] using ext j av,rfl⟩
  | node o l r il ir =>
    obtain ⟨al,ar⟩ := av
    let A := l.build ren w.length
    let u := run A.1 w
    have ul : u.length=w.length+A.1.length := length_run _ _
    let B := r.build ren u.length
    let v := run B.1 u
    have vl : v.length=w.length+A.1.length+B.1.length := by simp [v,length_run,ul]
    obtain ⟨la,ma,ba,sa⟩ := il w al nr ext
    obtain ⟨lb,mb,bb,sb⟩ := ir u ar (by omega) (fun j hj => by have := ext j hj; omega)
    change A.1.length=l.cost at la
    change B.1.length=r.cost at lb
    have sa' : v.getD A.2 false=l.value (fun i => w.getD i false) (fun j => w.getD (ren j) false) :=
      (earlier B.1 u A.2 (by rw [ul];exact ba)).trans sa
    have transport (t : Term) (ht : t.Avail n seen) :
        t.value (fun i => u.getD i false) (fun j => u.getD (ren j) false)=
        t.value (fun i => w.getD i false) (fun j => w.getD (ren j) false) := by
      induction t with
      | raw i => exact earlier A.1 w i (by change i<n at ht; omega)
      | ref j => exact earlier A.1 w _ (ext j ht)
      | node o a b ha hb => exact congrArg₂ (act o) (ha ht.1) (hb ht.2)
    have sb' := sb.trans (transport r ar)
    unfold Term.build
    change (let b := r.build ren (w.length+A.1.length); let gs := A.1++b.1++[binary o A.2 b.2]; gs.length=(Term.node o l r).cost ∧ Mono gs ∧ w.length+A.1.length+b.1.length<w.length+gs.length ∧ (run gs w).getD (w.length+A.1.length+b.1.length) false=_)
    rw [←ul]
    dsimp only
    change (A.1++B.1++[binary o A.2 B.2]).length=_ ∧ Mono _ ∧ u.length+B.1.length<_ ∧ _
    refine ⟨by simp [Term.cost,la,lb,Nat.add_assoc],?_,by change u.length+B.1.length < w.length+(A.1++B.1++[binary o A.2 B.2]).length; simp only [List.length_append,List.length_singleton]; omega,?_⟩
    · intro g hg
      rcases List.mem_append.mp hg with old|last
      · exact (List.mem_append.mp old).elim (ma g) (mb g)
      · obtain rfl := List.mem_singleton.mp last
        cases o <;> simp [binary,gateOp]
    · rw [append_run,append_run]
      change (v++[val (binary o A.2 B.2) v]).getD _ false=_
      rw [show u.length+B.1.length=v.length from (length_run _ _).symm,getD_new,show val (binary o A.2 B.2) v=act o (v.getD A.2 false) (v.getD B.2 false) from
        row_full (Row.mk o A.2 B.2 .both) v,sa',sb']
      rfl

end ThresholdFactorExpr
