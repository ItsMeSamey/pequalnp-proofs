import Numeric25057Closure
import SliceNext
import SliceBadW

namespace Probe25057
open ProbeFrontier PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

private theorem checked_row {tab : Array Numeric25057.Key}
    (cov : Numeric25057.Covered tab tab.size) {S : Finset (Mask (Fin 21))}
    {b t B T w : ℕ} (sl : LiveSlice target b t S) (hb : b ≤ B) (ht : t ≤ T)
    (checked : Numeric25057.checkChild tab (B,T,codes S) w = true) :
    (codes S).contains Numeric25057.goal = false ∧
      ∀ k ∈ Numeric25057.next B T (codes S), ∃ w, Numeric25057.checkChild tab k w = true := by
  unfold Numeric25057.checkChild at checked
  split at checked
  · have hi : tab[w/2]? = some (B,T,codes S) := by simpa using checked
    have lt : w/2 < tab.size := by
      by_contra hn
      have nope : tab[w/2]? = none := Array.getElem?_eq_none (by omega)
      simp [nope] at hi
    obtain ⟨proof,hp⟩ := cov (w/2) lt
    exact Numeric25057.row_children_checked hi hp
  · exact (slice_not_badW sl hb ht _ checked).elim

theorem slice_not_checked {tab : Array Numeric25057.Key} (cov : Numeric25057.Covered tab tab.size)
    {S : Finset (Mask (Fin 21))} {b t : ℕ} (sl : LiveSlice target b t S) :
    ∀ B T, b ≤ B → t ≤ T → ∀ w,
      Numeric25057.checkChild tab (B,T,codes S) w ≠ true := by
  induction sl with
  | finish =>
    intro B T hb ht w hw
    have h := (checked_row cov LiveSlice.finish hb ht hw).1
    have mem : Numeric25057.goal ∈ codes ({target} : Finset _) :=
      mem_codes.mpr ⟨target,by simp,encode_target⟩
    simpa [mem] using h
  | @step b t S P neg y op hy fresh rest ih =>
    intro B T hb ht w hw
    have children := (checked_row cov (LiveSlice.step op hy fresh rest) hb ht hw).2
    let cb := if neg then 0 else 1
    let ct := if neg then 1 else 0
    have bb : B-cb+cb=B := by change b+cb ≤ B at hb; omega
    have tt : T-ct+ct=T := by change t+ct ≤ T at ht; omega
    have member := exactOp_next (B-cb) (T-ct) op hy fresh
    change (_,_,_) ∈ Numeric25057.next (B-cb+cb) (T-ct+ct) _ at member
    rw [bb,tt] at member
    obtain ⟨code,ok⟩ := children _ member
    apply ih (B-cb) (T-ct) _ _ code ok
    · change b+cb ≤ B at hb; omega
    · change t+ct ≤ T at ht; omega

/-- The exact physical statement follows from a checked covering table and
its five root witnesses, allowing all unused gate budget. -/
theorem refute_of_ledger {tab : Array Numeric25057.Key} (cov : Numeric25057.Covered tab tab.size)
    (roots : ∀ t ≤ 4, ∃ w, Numeric25057.checkChild tab (9-t,t,Numeric25057.start) w = true) :
    ¬ ∃ C : Circuit, FanInTwo C ∧ C.size ≤ 9 ∧
      ∀ i j : Fin 6, C.eval (List.ofFn fun k : Fin 6 => decide (k=i ∨ k=j)) =
        (270585021 : ℕ).testBit (6*min i.val j.val+max i.val j.val) := by
  rintro ⟨C,fan,size,out⟩
  obtain ⟨B,T,budget,build⟩ := physical_to_build C fan size out
  obtain ⟨S,sub,b,hb,t,ht,sl⟩ := build.slice
  have init := subset_essential S sub (fun i j h => sl.asRun.separates i j h)
  subst S
  have card : start.card = 6 := by rw [←length_codes,codes_start]; decide
  have needed := sl.card_le
  have t4 : t≤4 := by omega
  obtain ⟨w,hw⟩ := roots t t4
  apply slice_not_checked cov sl (9-t) t (by omega) le_rfl w
  simpa only [codes_start,Numeric25057.start] using hw

end Probe25057
