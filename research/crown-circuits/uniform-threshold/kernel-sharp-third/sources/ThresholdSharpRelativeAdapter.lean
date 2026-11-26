import ThresholdSharpAggregate
import ThresholdSharpRegularMargin
namespace ThresholdSharpGlobalLower
open ThresholdThirdDeletion
/-- Same-graph inequalities at tolerance u.  z is the fine missing fraction.
Only the competing-cold cost enters the normalized fine loss. -/
structure RelativeLedger (m t E u : ℝ) where
  h : ℝ
  w : ℝ
  g : ℝ
  A : ℝ
  D : ℝ
  F : ℝ
  z : ℝ
  hubs : 0<h
  width : 0≤w
  fine : 0≤F
  missing : 0≤z
  wedge : 2*g^2≤w*((A+D)+g)
  rowError : 2*h^2-2*g^2+w*(g+A)≤u*h^2
  diagonal : D*w^4≤u*h^4
  nonedge : 2*D^2≤w^2*(4*F+D)
  loss : F≤(z+u)*h*E
  columns : w≤(1-z+u)*E
  colSign : 0≤1-z+u
  order : (1-u)*t≤h

theorem from_relative {m t E u : ℝ} (L : RelativeLedger m t E u) (mn : 0≤m)
    (en : 0≤E) (tn : 0≤t) (sq : t^2=2*m) (un : 0≤u) (small : u≤1/1000) :
    (1-1000*u)*coeff*m^3≤E^10 := by
  have step := ThresholdSharpAggregate.wedge_loss L.h L.w L.g (L.A+L.D) L.A L.D L.F u u
    L.width (by linarith) rfl L.wedge L.rowError L.diagonal L.nonedge
  have agg := ThresholdSharpAggregate.aggregate L.h E L.w L.F L.z u u u u
    L.hubs en L.width L.fine (by linarith [L.missing]) L.colSign step L.loss L.columns
  have a := pow_le_pow_left₀ (mul_nonneg (by linarith : 0≤1-u) tn) L.order 3
  have plus : 0≤3125*((2-u)^2/2-u/4) := by
    have lo : 1≤2-u := by linarith
    have b := pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1) lo 2
    nlinarith only [b,small]
  have lift := mul_le_mul_of_nonneg_left a plus
  apply regular_margin mn en tn sq un small
  nlinarith only [lift,agg,mul_pow (1-u) t 3,show 1+u+u=1+2*u by ring]

def BoundedRegular : Prop := ∀ B : ℝ,0<B → ∀ u : ℝ,0<u → u≤1/1000 →
  ∃ N : Nat, ∀ n : Nat,N≤n → RegularOrder n → 0≤surplus n → (surplus n)^10≤B*(n:ℝ)^3 →
    Nonempty (RelativeLedger (n:ℝ) (Real.sqrt (2*(n:ℝ))) (surplus n) u)

theorem regular_of_bounded (scale : BoundedRegular) : RegularLower := by
  intro B pos eps epos emax
  let u := eps/1000
  obtain ⟨N,h⟩ := scale B pos u (by dsimp [u]; positivity) (by dsimp [u]; linarith)
  refine ⟨N,?_⟩
  intro n large reg en upper
  obtain ⟨ledger⟩ := h n large reg en upper
  have bound := from_relative ledger (Nat.cast_nonneg n) en (Real.sqrt_nonneg _)
    (Real.sq_sqrt (by positivity)) (by dsimp [u]; positivity) (by dsimp [u]; linarith)
  have eq : 1000*u=eps := by dsimp [u]; ring
  rwa [eq] at bound
end ThresholdSharpGlobalLower
