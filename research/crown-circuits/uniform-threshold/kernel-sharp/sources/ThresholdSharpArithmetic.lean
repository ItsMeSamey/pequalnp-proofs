import ThresholdPublicShared
import ThresholdPublicMinimum
import ThresholdFourThirdsReal

namespace ThresholdSharpArithmetic
open ThresholdPublicMinimum PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open ResidualSurplus T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdSharedOrBudget

/-- The doubled final tally. Its variables are signed integers; h is the actual
number of shared OR gates, s is the signed surplus over two gates per input. -/
def Tally (n s h : ℤ) : Prop :=
  2*n ≤ 8+6*h+h*(h-1)+2*h*(s+1-h)

/-- e₀, e₁, e₂ are the three incidence classes. q is the number of shared
pairs, miss counts missing pairs, and dO,dA denote surplus fanout. -/
theorem tally_of_classes {n s h e₀ e₁ e₂ q miss dO dA : ℤ}
    (edges : n=e₀+e₁+e₂) (avoid : e₀≤4)
    (boundary : e₁≤3*h+dO+miss+(h-1)*dO+h*dA)
    (missing : miss+e₂≤q) (pairs : 2*q=h*(h-1))
    (budget : dO+dA=s+1-h) : Tally n s h := by
  unfold Tally
  have mult := congrArg (fun t : ℤ => h*t) budget
  nlinarith

def Bound (n s : ℤ) : Prop :=
  5 ≤ 2*s+7 ∧ 8*n-7 ≤ (2*s+7)^2

theorem regular {n s h : ℤ} (nonneg : 0≤h) (funded : h≤s+1)
    (tally : Tally n s h) : Bound n s := by
  unfold Tally at tally
  have gap := mul_nonneg (show 0≤s+1-h by omega) (show 0≤s+6-h by omega)
  constructor
  · omega
  · nlinarith

theorem base {g : ℤ} (hg : 7≤g) : Bound 4 (g-8) := by
  constructor
  · omega
  · nlinarith [mul_nonneg (show 0≤g-7 by omega) (show 0≤g-2 by omega)]

theorem deletion {n s s' : ℤ} (before : Bound n s) (saved : s+1≤s') :
    Bound (n+1) s' := by
  obtain ⟨pos,sq⟩ := before
  have factor := mul_nonneg (show 0≤s'-s-1 by omega) (show 0≤s'+s+8 by omega)
  constructor
  · omega
  · nlinarith

/-- This native step is unconditional: every regular representative spends
at least one mandatory read per nonoutput gate, irrespective of its OR layout. -/
theorem small_step (n : ℕ) (hn : 2≤n) :
    minimum n + 3 ≤ minimum (n+1) ∨ 2*(n+1) ≤ minimum (n+1)+1 := by
  obtain ⟨C,mono,correct,cost⟩ := attained (n+1)
  rcases ThresholdPublicShared.shared_or_delete hn C mono correct with
    ⟨D,hm,hd,hs⟩ | ⟨gs,out,M,reg,size,budget,_⟩
  · exact Or.inl (cost ▸ (Nat.add_le_add_right (le_size hm hd) 3).trans hs)
  · exact Or.inr (by omega)

theorem minimum_three : 4 ≤ minimum 3 := by
  have step := small_step 2 (by decide)
  have bot := base_one
  norm_num at step
  omega

theorem minimum_four : 7 ≤ minimum 4 := by
  have step := small_step 3 (by decide)
  have bot := minimum_three
  norm_num at step
  omega

/-- Sole additional circuit hypothesis: verify the displayed double-count on
each actual regular lex-minimizer of arity at least five. All funding, small
arities, physical deletion, and passage to arbitrary competitors are internal. -/
def PhysicalTally : Prop :=
  ∀ (n : ℕ), 5 ≤ n → ∀ (gs : List Raw) (out : ℕ),
    LexMinimum n (source gs out) → Regular n gs →
    Tally (n:ℤ) (((source gs out).size:ℤ)-2*(n:ℤ))
      (((sharedOrs (source gs out) n).length:ℤ))

theorem minimum_squared (counted : PhysicalTally) {n : ℕ} (hn : 4≤n) :
    Bound (n:ℤ) (ThresholdFourThirds.excess intMinimum n) := by
  have aux : ∀ k : ℕ, Bound ((k+4:ℕ):ℤ) (ThresholdFourThirds.excess intMinimum (k+4)) := by
    intro k
    induction k with
    | zero =>
      have hb : (7:ℤ)≤ intMinimum 4 := by exact_mod_cast minimum_four
      simpa [ThresholdFourThirds.excess] using base hb
    | succ k ih =>
      let m := k+4
      have hm : 2≤m := by dsimp [m]; omega
      change Bound (((m+1:ℕ):ℤ)) (ThresholdFourThirds.excess intMinimum (m+1))
      obtain ⟨C,mono,correct,cost⟩ := attained (m+1)
      rcases ThresholdPublicShared.shared_or_delete hm C mono correct with
        ⟨D,hD,drep,save⟩ | ⟨gs,out,M,reg,size,fund,_⟩
      · have pay := (Nat.add_le_add_right (le_size hD drep) 3).trans save
        rw [cost] at pay
        have pay' : intMinimum m + 3 ≤ intMinimum (m+1) := by exact_mod_cast pay
        have changeS : ThresholdFourThirds.excess intMinimum m + 1 ≤
            ThresholdFourThirds.excess intMinimum (m+1) := by
          unfold ThresholdFourThirds.excess
          push_cast
          omega
        change Bound (m:ℤ) (ThresholdFourThirds.excess intMinimum m) at ih
        rw [Nat.cast_add, Nat.cast_one]
        exact deletion ih changeS
      · let B := source gs out
        let h := (sharedOrs B (m+1)).length
        have eqsize : B.size = minimum (m+1) := lex_size (by omega) M
        have pay : h+2*(m+1) ≤ minimum (m+1)+1 := by
          change h+2*(m+1) ≤ B.size+1 at fund
          rwa [eqsize] at fund
        have pay' : (h:ℤ)+2*((m+1:ℕ):ℤ) ≤ intMinimum (m+1)+1 := by exact_mod_cast pay
        have hh : (h:ℤ)≤ ThresholdFourThirds.excess intMinimum (m+1)+1 := by
          unfold ThresholdFourThirds.excess
          omega
        apply regular (h:=(h:ℤ)) (by exact_mod_cast (Nat.zero_le h)) hh
        have tc := counted (m+1) (by dsimp [m]; omega) gs out M reg
        change Tally ((m+1:ℕ):ℤ) ((B.size:ℤ)-2*((m+1:ℕ):ℤ)) (h:ℤ) at tc
        simpa only [eqsize,ThresholdFourThirds.excess,intMinimum] using tc
  have eqn : n-4+4=n := by omega
  simpa only [eqn] using aux (n-4)

theorem minimum_real (counted : PhysicalTally) {n : ℕ} (hn : 4≤n) :
    2*(n:ℝ)+(Real.sqrt (8*(n:ℝ)-7)-7)/2 ≤ (minimum n:ℝ) := by
  obtain ⟨hp,hq⟩ := minimum_squared counted hn
  unfold ThresholdFourThirds.excess intMinimum at hp hq
  have hp' : (5:ℝ) ≤ 2*((minimum n:ℝ)-2*(n:ℝ))+7 := by exact_mod_cast hp
  have hq' : 8*(n:ℝ)-7 ≤ (2*((minimum n:ℝ)-2*(n:ℝ))+7)^2 := by exact_mod_cast hq
  have hn' : (4:ℝ) ≤ (n:ℝ) := by exact_mod_cast hn
  have root := Real.sq_sqrt (show 0≤8*(n:ℝ)-7 by linarith)
  by_contra! bad
  have contradiction := mul_pos
    (show 0<Real.sqrt (8*(n:ℝ)-7)-(2*((minimum n:ℝ)-2*(n:ℝ))+7) by linarith)
    (show 0<Real.sqrt (8*(n:ℝ)-7)+(2*((minimum n:ℝ)-2*(n:ℝ))+7) by
      linarith [Real.sqrt_nonneg (8*(n:ℝ)-7)])
  nlinarith

end ThresholdSharpArithmetic
