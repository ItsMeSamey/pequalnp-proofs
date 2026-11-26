import ThresholdUniformGraphErrors
import ThresholdSharpRelativeAdapter
namespace ThresholdSharpGlobalLower
/-- The coarse pool controls degrees; only the fine pool is used in the final nonedge moment. -/
theorem graph_ledger {m t P X h E w g A D coarse holes u : ℝ}
    (huge : 1048576≤P) (scale : P^100≤X) (tol : 1≤P*u)
    (hlo : X^10≤2*h) (hhi : h≤2*X^10) (elo : X^6≤65536*E)
    (hp : 0<h) (ep : 0<E) (wg : 0≤w) (gg : 0≤g) (ap : 0≤A) (dp : 0≤D)
    (cp : 0≤coarse) (lp : 0≤holes)
    (gh : g≤h) (rows : h-g≤P^3*X^8) (width : w≤P^2*X^6)
    (cap : coarse≤6*P^2*X^16)
    (adj : A^2≤g*(A+D+6*coarse)) (nc : 2*D^2≤w^2*(4*coarse+D))
    (nf : 2*D^2≤w^2*(4*(holes+4*(A+D)+4*g)+D))
    (wed : 2*g^2≤w*((A+D)+g))
    (cols : w≤(1-holes/(h*E)+u)*E)
    (order : (1-u)*t≤h) : Nonempty (RelativeLedger m t E u) := by
  obtain ⟨_,_,cost,row,dia,_⟩ := ThresholdUniformGraphErrors.bounds huge scale tol hlo hhi elo wg gg ap dp cp
    gh rows width cap (show coarse≤coarse+4*(A+D)+4*g by linarith) adj nc
  have he : 0<h*E := mul_pos hp ep
  have split : holes/(h*E)*(h*E)=holes := div_mul_cancel₀ _ he.ne'
  refine ⟨⟨h,w,g,A,D,holes+4*(A+D)+4*g,holes/(h*E),hp,wg,by positivity,
    div_nonneg lp he.le,wed,row,dia,nf,?_,cols,?_,order⟩⟩
  · nlinarith only [cost,split]
  · by_contra! bad
    exact (not_lt_of_ge (wg.trans cols)) (mul_neg_of_neg_of_pos bad ep)
end ThresholdSharpGlobalLower
