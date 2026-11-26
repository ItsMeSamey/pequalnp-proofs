import T2SoleOrEval
import Mathlib.Data.Finset.Card

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



/-- Map the shortened gate list back to the original row indices. -/
def skipRow (h j : Nat) := if j<h then j else j+1

private theorem skip_inj (h : Nat) : Function.Injective (skipRow h) := by
  intro a b eq; unfold skipRow at eq; split at eq <;> split at eq <;> omega

private theorem skip_avoids (h j : Nat) : skipRow h j ≠ h := by
  unfold skipRow; split <;> omega

private theorem ren_skip (n h x j : Nat) :
    ren (n+h) x (n+skipRow h j) = n+j := by
  unfold skipRow
  split <;> rename_i lt
  · simp [ren,show n+j<n+h by omega]
  · simp only [ren,if_neg (by omega : ¬n+(j+1)<n+h),if_neg (by omega : n+(j+1)≠n+h)]
    omega

def singletonHot (n : Nat) (C : Circuit) (j : Nat) : Prop :=
  ∃ i : Fin n, (C.wires (vector {i})).getD (n+j) false=true

noncomputable def hotSet (n : Nat) (C : Circuit) : Finset Nat := by
  classical
  exact ((List.range C.gates.length).filter (fun j => decide (singletonHot n C j))).toFinset

private theorem in_hotSet (n : Nat) (C : Circuit) (j : Nat) :
    j∈hotSet n C ↔ j<C.gates.length ∧ singletonHot n C j := by
  classical
  simp [hotSet]

private theorem hotSet_card (n : Nat) (C : Circuit) :
    (hotSet n C).card=hotRows n C := by
  classical
  unfold hotSet hotRows singletonHot
  rw [List.toFinset_card_of_nodup (List.nodup_range.filter _)]
  congr 1
  apply List.filter_congr
  intro j _
  apply Bool.eq_iff_iff.mpr
  simp

theorem hot_count_of_retained (n h t : Nat) (C D : Circuit)
    (lc : C.gates.length=h+1+t) (ld : D.gates.length=h+t+1)
    (hot : singletonHot n C h) (cold : ¬ singletonHot n D (h+t))
    (compare : ∀ j, j<h+t → singletonHot n D j → singletonHot n C (skipRow h j)) :
    hotRows n D < hotRows n C := by
  classical
  let S := hotSet n D
  let T := hotSet n C
  have absent : h ∉ S.image (skipRow h) := by
    intro hx
    obtain ⟨j,_,eq⟩ := Finset.mem_image.mp hx
    exact skip_avoids h j eq
  have bound : insert h (S.image (skipRow h)) ⊆ T := by
    intro k hk
    rcases Finset.mem_insert.mp hk with eq|image
    · subst k; exact (in_hotSet n C h).mpr ⟨by omega,hot⟩
    · obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp image
      obtain ⟨within,on⟩ := (in_hotSet n D j).mp hj
      have ne : j≠h+t := by rintro rfl; exact cold on
      have lt : j<h+t := by omega
      refine (in_hotSet n C _).mpr ⟨?_,compare j lt on⟩
      unfold skipRow; split <;> omega
  have sz := Finset.card_le_card bound
  rw [Finset.card_insert_of_notMem absent,Finset.card_image_of_injective S (skip_inj h)] at sz
  change (hotSet n D).card+1 ≤ (hotSet n C).card at sz
  rw [hotSet_card,hotSet_card] at sz
  omega

theorem moved_hotRows_lt (n x p : Nat) (pre post : List Gate) (out : Nat)
    (hx : x<n) (ok : SuffixOK (n+pre.length+1) post)
    (computes : Computes n (moved n x p pre post out)) :
    hotRows n (moved n x p pre post out) <
      hotRows n (⟨pre ++ binary .or x p :: post,out⟩ : Circuit) := by
  let C : Circuit := ⟨pre ++ binary .or x p :: post,out⟩
  let D := moved n x p pre post out
  let J := short n x pre post out
  apply hot_count_of_retained n pre.length post.length C D
  · simp [C] <;> omega
  · simp [D,moved,short,Nat.add_assoc]
  · let i : Fin n := ⟨x,hx⟩
    refine ⟨i,?_⟩
    let v := vector ({i} : Finset (Fin n))
    have vl : v.length=n := by simp [v,vector]
    have xpos : v.getD x false=true := by simp [v,vector,List.getD_eq_getElem?_getD,hx,i]
    have hit : (run pre v).getD x false=true := by
      rw [run_old _ _ _ (by omega),xpos]
    have plen : (run pre v).length=n+pre.length := by simp [run_len,vl]
    change (run (pre ++ binary .or x p :: post) v).getD (n+pre.length) false=true
    rw [run_app]
    change (run post (run pre v ++ [val (binary .or x p) (run pre v)])).getD (n+pre.length) false=true
    rw [run_old _ _ _ (by simp [plen]),←plen,getD_new,val_or,hit] <;> rfl
  · rintro ⟨i,on⟩
    have obs : D.output=n+(pre.length+post.length) := by simp [D,moved,short]
    have accepted : D.eval (vector {i})=true := by simpa only [Circuit.eval,obs] using on
    have card := (computes {i}).mp accepted
    simpa using card
  · intro j hj hit
    obtain ⟨i,hi⟩ := hit
    refine ⟨i,?_⟩
    let v := vector ({i} : Finset (Fin n))
    have vl : v.length=n := by simp [v,vector]
    have fit : n+skipRow pre.length j<n+pre.length+1+post.length := by
      unfold skipRow; split <;> omega
    have rel := (short_wires pre post x p out _ n v vl hx ok fit).1
    rw [ren_skip] at rel
    apply rel
    have within : n+j < (run J.gates v).length := by simp [J,short,run_len,vl] <;> omega
    change (run (J.gates++[binary .or J.output p]) v).getD (n+j) false=true at hi
    rw [run_app,run_old _ _ _ within] at hi
    exact hi

#print axioms moved_hotRows_lt
end T2SoleOrSplice
