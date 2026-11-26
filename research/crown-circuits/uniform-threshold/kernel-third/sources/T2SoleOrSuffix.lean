import T2SoleOrSplice

namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus

/-- New bit implies old bit. On assignments satisfying E they coincide. -/
def Related (E : Prop) (a b : Bool) := (a=true → b=true) ∧ (E → a=b)

private theorem rel_act {E : Prop} (o : Op) {a b c d : Bool}
    (l : Related E a b) (r : Related E c d) :
    Related E (act o a c) (act o b d) := by
  obtain ⟨ld,leq⟩ := l
  obtain ⟨rd,req⟩ := r
  constructor
  · cases o <;> cases a <;> cases b <;> cases c <;> cases d <;> first | exact id | exact fun _ => rfl | exact fun h => False.elim (Bool.noConfusion h) | exact fun _ => ld rfl | exact fun _ => rd rfl
  · intro he
    rw [leq he,req he]

private theorem old_get (u : List Bool) (a : Bool) (i : Nat) (lt : i<u.length) :
    (u++[a]).getD i false=u.getD i false := by
  simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]

/-- The shortened and original buffers differ in length by exactly one. -/
structure Aligned (E : Prop) (h x : Nat) (u v : List Bool) : Prop where
  width : v.length=u.length+1
  passed : h<v.length
  raw : x<h
  atWire : ∀ i, i<v.length → Related E (u.getD (ren h x i) false) (v.getD i false)

private theorem ren_inside {h x i k : Nat} (hx : x<h) (hk : h<k) (hi : i<k) :
    ren h x i < k-1 := by
  by_cases a : i<h
  · simp only [ren,if_pos a]; omega
  · by_cases b : i=h
    · simp only [ren,if_neg a,if_pos b]; omega
    · simp only [ren,if_neg a,if_neg b]; omega

theorem Aligned.push {E : Prop} {h x : Nat} {u v : List Bool}
    (pair : Aligned E h x u v) {a b : Bool} (new : Related E a b) :
    Aligned E h x (u++[a]) (v++[b]) := by
  obtain ⟨width,passed,hx,wires⟩ := pair
  refine ⟨by simp [width],by simp; omega,hx,?_⟩
  intro i hi
  simp only [List.length_append,List.length_singleton] at hi
  by_cases old : i<v.length
  · have fit := ren_inside hx passed old
    have small : ren h x i < u.length := by omega
    rw [old_get _ _ _ small,old_get _ _ _ old]
    exact wires i old
  · have endi : i=v.length := by omega
    subst i
    have shift : ren h x v.length=u.length := by
      simp only [ren,if_neg (by omega : ¬v.length<h),if_neg (by omega : ¬v.length=h)]
      omega
    rw [shift,getD_new,getD_new]; exact new

/-- Exact valid binary suffix, expressed without reliance on a separate gate structure. -/
def SuffixOK : Nat → List Gate → Prop
  | _,[] => True
  | k,g::gs => (∃ o : Op, ∃ l r : Nat, g=binary o l r ∧ l<k ∧ r<k) ∧ SuffixOK (k+1) gs

theorem aligned_suffix (gs : List Gate) {E : Prop} {h x : Nat} {u v : List Bool}
    (pair : Aligned E h x u v) (ok : SuffixOK v.length gs) :
    Aligned E h x (run (gs.map (rewire (ren h x))) u) (run gs v) := by
  induction gs generalizing u v with
  | nil => exact pair
  | cons g gs ih =>
    obtain ⟨⟨o,l,r,rfl,hl,hr⟩,tail⟩ := ok
    have bit := rel_act o (pair.atWire l hl) (pair.atWire r hr)
    have eq1 : rewire (ren h x) (binary o l r) = binary o (ren h x l) (ren h x r) := rfl
    have valbin (op : Op) (i j : Nat) (w : List Bool) :
        val (binary op i j) w=act op (w.getD i false) (w.getD j false) :=
      row_full (Row.mk op i j .both) w
    simp only [List.map_cons,eq1]
    change Aligned E h x (run _ (u++[val (binary o (ren h x l) (ren h x r)) u]))
                           (run gs (v++[val (binary o l r) v]))
    apply ih
    · apply pair.push
      simpa only [valbin] using bit
    · simpa using tail

/-- Initial alignment immediately after skipping the old reader row. -/
theorem start_skip (v : List Bool) (x p : Nat) (hx : x<v.length) :
    Aligned (v.getD p false=false) v.length x v
      (v++[v.getD x false || v.getD p false]) := by
  refine ⟨by simp,by simp,hx,?_⟩
  intro i hi
  simp only [List.length_append,List.length_singleton] at hi
  by_cases small : i<v.length
  · simp only [ren,if_pos small,old_get _ _ _ small]
    exact ⟨id,fun _ => rfl⟩
  · have last : i=v.length := by omega
    subst i
    have rr : ren v.length x v.length=x := by simp [ren]
    rw [rr,getD_new]
    constructor
    · intro h; rw [h] <;> rfl
    · intro e; rw [e,Bool.or_false]

/-- For every retained physical wire, compare the two concrete suffix evaluations. -/
theorem bypass_suffix_wires (post : List Gate) (buf : List Bool) (x p i : Nat)
    (hx : x<buf.length) (ok : SuffixOK (buf.length+1) post)
    (fit : i<(run post (buf++[buf.getD x false || buf.getD p false])).length) :
    Related (buf.getD p false=false)
      ((run (post.map (rewire (ren buf.length x))) buf).getD (ren buf.length x i) false)
      ((run post (buf++[buf.getD x false || buf.getD p false])).getD i false) := by
  exact (aligned_suffix post (start_skip buf x p hx) (by simpa using ok)).atWire i fit

end T2SoleOrSplice
