import T2SoleOrClean
import T2SoleOrEdit
namespace T2SoleOrSplice
open PEqualNP.CircuitLowerBounds ResidualSurplus T2RawIsolation

def original (swap : Bool) (pre post : List Gate) (x p out : Nat) : Circuit :=
  ⟨pre ++ reader swap x p :: post,out⟩

theorem order_wires (swap : Bool) (pre post : List Gate) (x p out : Nat) (w : List Bool) :
    (original swap pre post x p out).wires w=(original false pre post x p out).wires w := by
  simp only [original,Circuit.wires,List.foldl_append,List.foldl_cons]
  change run post (run pre w++[val (reader swap x p) (run pre w)]) =
    run post (run pre w++[val (reader false x p) (run pre w)])
  rw [reader_bit,reader_bit]

theorem order_hot (swap : Bool) (pre post : List Gate) (x p out n : Nat) :
    hotRows n (original swap pre post x p out)=hotRows n (original false pre post x p out) := by
  classical
  unfold hotRows
  simp only [order_wires swap pre post x p out]
  simp only [original,List.length_append,List.length_cons]

private theorem length_run (gs : List Gate) (w : List Bool) :
    (run gs w).length=w.length+gs.length := by
  induction gs generalizing w with
  | nil => simp [run]
  | cons g gs ih =>
    change (run gs (w++[val g w])).length=_
    rw [ih]; simp <;> omega

private theorem unchanged_raw (gs : List Gate) (w : List Bool) (j : Nat) (hi : j<w.length) :
    (run gs w).getD j false=w.getD j false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change (run gs (w++[val g w])).getD j false=_
    rw [ih _ (by simp; omega)]
    simp [List.getD_eq_getElem?_getD,List.getElem?_append_left hi]

theorem duplicate_computes (n x out : Nat) (pre post : List Gate)
    (old : Computes n (original false pre post x x out)) (hx : x<n)
    (tail : SuffixOK (n+pre.length+1) post) (fit : out<n+pre.length+1+post.length) :
    Computes n (short n x pre post out) := by
  intro s
  let w := vector s
  let v := run pre w
  have len : v.length=n+pre.length := by simp [v,w,length_run,vector]
  have lt : x<v.length := by omega
  have seed : Aligned True v.length x v (v++[v.getD x false]) := by
    refine ⟨by simp,by simp,lt,?_⟩
    intro i hi
    by_cases small : i<v.length
    · simp only [ren,if_pos small]
      have eq : (v++[v.getD x false]).getD i false=v.getD i false := by
        simp [List.getD_eq_getElem?_getD,List.getElem?_append_left small]
      rw [eq]; exact ⟨id,fun _ => rfl⟩
    · have eq : i=v.length := by simp at hi; omega
      subst i
      simp only [ren,lt_self_iff_false,if_false,if_pos rfl,getD_new]
      exact ⟨id,fun _ => rfl⟩
  have full := aligned_suffix post seed (by simpa [len] using tail)
  have eq := (full.atWire out (by simpa [length_run,len] using fit)).2 trivial
  have sim : (short n x pre post out).eval w=(original false pre post x x out).eval w := by
    change (run (pre ++ post.map _) w).getD _ false =
      (run (pre ++ reader false x x :: post) w).getD out false
    have app (a b : List Gate) : run (a++b) w=run b (run a w) := by simp [run,List.foldl_append]
    rw [app,app]
    change _ = (run post (v++[val (reader false x x) v])).getD out false
    rw [reader_bit,Bool.or_self]
    change (run (post.map (rewire (ren (n+pre.length) x))) v).getD (ren (n+pre.length) x out) false = _
    simpa only [len] using eq
  change (short n x pre post out).eval w=true ↔ _
  rw [sim]; exact old s

theorem no_sole_reader (n : Nat) (x : Fin n) (p out : Nat) (pre post : List Gate) (swap : Bool)
    (old : Eligible n (original swap pre post x.val p out))
    (primary : ∀ D, Eligible n D → (original swap pre post x.val p out).size≤D.size)
    (secondary : SecondaryMinimum n (original swap pre post x.val p out))
    (left : ∀ g∈pre,x.val∉g.inputs) (right : ∀ g∈post,x.val∉g.inputs) : False := by
  let C := original swap pre post x.val p out
  let F := original false pre post x.val p out
  have sameEv (w : List Bool) : C.eval w=F.eval w := congrArg (fun v : List Bool => v.getD out false) (order_wires swap pre post x.val p out w)
  have oc : Computes n F := by intro s; rw [←sameEv]; exact old.1 s
  have oldV := ((eligible_iff _ _).mp old).2
  have origLen : out<n+pre.length+1+post.length := by
    have := oldV.1; simp [original,Circuit.size] at this; omega
  have h := (ok_append pre _ n).mp oldV.2
  have tail : SuffixOK (n+pre.length+1) post := h.2.2
  obtain ⟨op,l,r,hr,hl,hright⟩ := h.2.1
  have hp : p<n+pre.length := by
    cases swap <;> simp [reader,binary] at hr <;> grind
  have hx : x.val<n+pre.length := by omega
  have fc : Eligible n F := by
    apply (eligible_iff _ _).mpr
    refine ⟨oc,by simpa [F,original,Circuit.size] using oldV.1,(ok_append pre _ n).mpr ⟨h.1,?_,tail⟩⟩
    exact ⟨.or,x.val,p,rfl,hx,hp⟩
  by_cases dup : p=x.val
  · subst p
    let J := short n x.val pre post out
    have level : SuffixOK n J.gates := by
      apply (ok_append pre _ n).mpr
      simpa using And.intro h.1 (ok_rename post (n+pre.length) x.val (n+pre.length+1) hx (by omega) tail)
    have bound : J.output<n+J.size := by
      change ren (n+pre.length) x.val out<n+(pre++post.map _).length
      simp only [List.length_append,List.length_map]
      unfold ren
      split <;> (first | omega | split <;> omega)
    have good := (eligible_iff n J).mpr ⟨duplicate_computes _ _ _ _ _ oc x.isLt tail origLen,bound,level⟩
    have cost := primary J good
    simp [J,original,short,Circuit.size] at cost <;> omega
  · have notOut : out≠x.val := by
      intro eq
      have valx : C.eval (vector {x})=true := by
        change (run C.gates (vector {x})).getD out false=true
        rw [eq,unchanged_raw _ _ _ (by simp [vector]),vec_get]
        simp [x.isLt]
      have := (old.1 {x}).mp valx
      simp at this
    have clean := sole_clean n x p out pre post swap dup notOut h.1 old.1 left right
    have minF : SecondaryMinimum n F := by
      intro D good eq
      rw [←order_hot swap pre post x.val p out n]
      exact secondary D good (by simpa [F,original,Circuit.size] using eq)
    exact no_clean_or_at_secondary_minimum n x.val p pre post out fc minF x.isLt hp clean
#print axioms no_sole_reader
end T2SoleOrSplice
