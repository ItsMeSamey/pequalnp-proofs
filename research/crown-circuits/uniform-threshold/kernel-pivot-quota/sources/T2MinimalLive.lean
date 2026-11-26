import Batteries.Tactic.OpenPrivate
import T2LexMinimum
import T2SoleOrTopology
import T2ReaderConsumer

namespace T2MinimalLive
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2RawIsolation
open private run_app run_len from T2SoleOrEval
open private rename_bound from T2SoleOrTopology

private theorem skip_alias (v : List Bool) (x : Nat) (lt : x<v.length) :
    Aligned True v.length x v (v++[v.getD x false]) := by
  refine ⟨by simp,by simp,lt,?_⟩
  intro i hi
  by_cases old : i<v.length
  · simp [ren,old,List.getD_eq_getElem?_getD,List.getElem?_append_left old,Related]
  · have last : i=v.length := by simp only [List.length_append,List.length_singleton] at hi; omega
    subst i; rw [getD_new]; simp [ren,Related]

theorem dead_short (n x out : Nat) (pre post : List Gate) (g : Gate)
    (hx : x<n+pre.length) (wf : SuffixOK (n+pre.length+1) post)
    (bound : out<n+pre.length+1+post.length) (obs : out≠n+pre.length)
    (dead : ∀ a∈post, n+pre.length∉a.inputs) (w : List Bool) (hw : w.length=n) :
    (short n x pre post out).eval w = (⟨pre++g::post,out⟩ : Circuit).eval w := by
  let v := run pre w
  have width : v.length=n+pre.length := by simp [v,run_len,hw]
  let fake := v++[v.getD x false]
  let real := v++[val g v]
  have cmp := aligned_suffix post (skip_alias v x (by omega)) (by simpa [width] using wf)
  have fit : out<(run post fake).length := by simpa [fake,run_len,width,Nat.add_assoc] using bound
  have keep := (cmp.atWire out fit).2 trivial
  have drop := unread_run post (T2ReaderConsumer.agree_last v (v.getD x false) (val g v))
    (fun a ha => by simpa [width] using dead a ha)
  have eq := drop.2 out (by simpa [width] using obs)
  change (run (pre++post.map (rewire (ren (n+pre.length) x))) w).getD (ren (n+pre.length) x out) false =
    (run (pre++g::post) w).getD out false
  rw [run_app,run_app]
  change (run (post.map (rewire (ren (n+pre.length) x))) v).getD (ren (n+pre.length) x out) false =
    (run post (v++[val g v])).getD out false
  simpa only [width] using keep.trans eq

private theorem forbids_short (n x out : Nat) (pre post : List Gate) (g : Gate)
    (minC : LexMinimum n ⟨pre++g::post,out⟩) (hx : x<n+pre.length)
    (same : Computes n (short n x pre post out)) : False := by
  let C : Circuit := ⟨pre++g::post,out⟩
  let D := short n x pre post out
  have orig := (eligible_iff n C).mp minC.eligible
  have bound : out<n+pre.length+1+post.length := by
    simpa [C,Circuit.size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using orig.2.1
  have cut := (ok_append pre (g::post) n).mp orig.2.2
  have suffix : SuffixOK (n+pre.length+1) post := cut.2.2
  have shape : SuffixOK n D.gates := by
    apply (ok_append _ _ _).mpr
    exact ⟨cut.1,by simpa using ok_rename post (n+pre.length) x (n+pre.length+1) hx (by omega) suffix⟩
  have output : D.output<n+D.size := by
    have h := rename_bound (h:=n+pre.length) (x:=x) (k:=n+pre.length+1+post.length)
      (j:=out) hx (by omega) bound
    change ren (n+pre.length) x out<n+(pre++post.map _).length
    simp only [List.length_append,List.length_map]; omega
  have good : Eligible n D := (eligible_iff _ _).mpr ⟨same,output,shape⟩
  have impossible := minC.primary D good
  simp [D,Circuit.size,short] at impossible <;> omega


theorem consumer_at_minimum (n x out : Nat) (pre post : List Gate) (g : Gate)
    (minC : LexMinimum n ⟨pre++g::post,out⟩)
    (hx : x<n+pre.length) (obs : out≠n+pre.length) :
    ∃ a∈post, n+pre.length∈a.inputs := by
  by_contra! dead
  have orig := (eligible_iff n _).mp minC.eligible
  have bound : out<n+pre.length+1+post.length := by
    simpa [Circuit.size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using orig.2.1
  have suffix : SuffixOK (n+pre.length+1) post :=
    ((ok_append pre (g::post) n).mp orig.2.2).2.2
  apply forbids_short n x out pre post g minC hx
  intro s
  rw [dead_short n x out pre post g hx suffix bound obs dead _ (by simp [vector])]
  exact orig.1 s

theorem no_duplicate_at_minimum (n x out : Nat) (pre post : List Gate) (o : Op)
    (minC : LexMinimum n ⟨pre++binary o x x::post,out⟩)
    (hx : x<n+pre.length) : False := by
  have orig := (eligible_iff n _).mp minC.eligible
  have bound : out<n+pre.length+1+post.length := by
    simpa [Circuit.size,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using orig.2.1
  have suffix : SuffixOK (n+pre.length+1) post :=
    ((ok_append pre (binary o x x::post) n).mp orig.2.2).2.2
  apply forbids_short n x out pre post (binary o x x) minC hx
  intro s
  let w := vector s
  let v := run pre w
  have width : v.length=n+pre.length := by simp [v,w,run_len,vector]
  have isAlias : val (binary o x x) v=v.getD x false := by
    cases o <;> simp [val,binary,gateOp,GateOp.eval]
  have cmp := aligned_suffix post (skip_alias v x (by omega)) (by simpa [width] using suffix)
  have keep := (cmp.atWire out (by simpa [run_len,width,Nat.add_assoc] using bound)).2 trivial
  have same : (short n x pre post out).eval w =
      (⟨pre++binary o x x::post,out⟩ : Circuit).eval w := by
    change (run (pre++post.map (rewire (ren (n+pre.length) x))) w).getD (ren (n+pre.length) x out) false =
      (run (pre++binary o x x::post) w).getD out false
    rw [run_app,run_app]
    change _ = (run post (v++[val (binary o x x) v])).getD out false
    rw [isAlias]
    simpa only [width] using keep
  change (short n x pre post out).eval w=true ↔ _
  rw [same]; exact orig.1 s

#print axioms no_duplicate_at_minimum
#print axioms consumer_at_minimum
end T2MinimalLive
