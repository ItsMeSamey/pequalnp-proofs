import T2SoleOrSuffix

namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus

private theorem run_app (gs hs : List Gate) (w : List Bool) :
    run (gs++hs) w=run hs (run gs w) := by simp [run,List.foldl_append]

private theorem run_len (gs : List Gate) (w : List Bool) : (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[val g w])).length=_
    rw [ih]; simp; omega

private theorem run_old (gs : List Gate) (w : List Bool) (i : Nat) (lt : i<w.length) :
    (run gs w).getD i false=w.getD i false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD i false=_
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left lt]

private theorem val_or (x p : Nat) (w : List Bool) :
    val (binary .or x p) w=(w.getD x false || w.getD p false) :=
  row_full (Row.mk .or x p .both) w

/-- The same comparison on original and shortened Circuit.wires, with
every row named by its old physical wire index. -/
theorem short_wires (pre post : List Gate) (x p out i n : Nat) (w : List Bool)
    (arity : w.length=n) (hx : x<n) (ok : SuffixOK (n+pre.length+1) post)
    (fit : i<n+pre.length+1+post.length) :
    Related ((run pre w).getD p false=false)
      (((short n x pre post out).wires w).getD (ren (n+pre.length) x i) false)
      (((⟨pre ++ binary .or x p :: post,out⟩ : Circuit).wires w).getD i false) := by
  have len : (run pre w).length=n+pre.length := by simp [run_len,arity]
  have core := bypass_suffix_wires post (run pre w) x p i (by omega)
    (by simpa [len] using ok) (by simpa [run_len,len] using fit)
  change Related _ ((run (pre ++ post.map _) w).getD _ false)
    ((run (pre ++ binary .or x p :: post) w).getD i false)
  rw [run_app,run_app]
  change Related _ _ ((run post (run pre w ++ [val (binary .or x p) (run pre w)])).getD i false)
  rw [val_or]
  simpa only [len] using core

theorem moved_eval (pre post : List Gate) (n x p out : Nat) (w : List Bool)
    (arity : w.length=n) (hp : p<n+pre.length) :
    (moved n x p pre post out).eval w =
      ((short n x pre post out).eval w || (run pre w).getD p false) := by
  let J := short n x pre post out
  have len : (run J.gates w).length=n+J.gates.length := by simp [run_len,arity]
  have prior : (run J.gates w).getD p false=(run pre w).getD p false := by
    change (run (pre ++ post.map _) w).getD p false=_
    rw [run_app,run_old _ _ _ (by simpa [run_len,arity] using hp)]
  change (run (J.gates ++ [binary .or J.output p]) w).getD (n+J.gates.length) false =
    ((run J.gates w).getD J.output false || (run pre w).getD p false)
  rw [run_app]
  change ((run J.gates w)++[val (binary .or J.output p) (run J.gates w)]).getD _ false=_
  rw [←len,getD_new,val_or,prior]

theorem moved_computes (n x p out : Nat) (pre post : List Gate)
    (old : Computes n ⟨pre ++ binary .or x p :: post,out⟩)
    (hx : x<n) (hp : p<n+pre.length) (outOK : out<n+pre.length+1+post.length)
    (ok : SuffixOK (n+pre.length+1) post)
    (clean : ∀ s : Finset (Fin n), s.card<2 → (run pre (vector s)).getD p false=false) :
    Computes n (moved n x p pre post out) := by
  intro s
  have arity : (vector s).length=n := by simp [vector]
  rw [moved_eval pre post n x p out _ arity hp]
  have cmp := (short_wires pre post x p out out n (vector s) arity hx ok outOK).2
  by_cases quiet : (run pre (vector s)).getD p false=false
  · have he : (short n x pre post out).eval (vector s) =
        (⟨pre ++ binary .or x p :: post,out⟩ : Circuit).eval (vector s) := cmp quiet
    rw [quiet,Bool.or_false,he]; exact old s
  · have threshold : 2≤s.card := by
      by_contra! small
      exact quiet (clean s small)
    cases valp : (run pre (vector s)).getD p false <;> simp_all

end T2SoleOrSplice
