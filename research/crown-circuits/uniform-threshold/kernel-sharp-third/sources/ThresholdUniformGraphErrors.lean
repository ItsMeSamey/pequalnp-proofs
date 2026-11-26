import ThresholdSharpGrowth
namespace ThresholdUniformGraphErrors

/-- Compare scale monomials. A strictly spare X exponent can absorb up to
one hundred powers of P, including the explicit scalar coefficient. -/
private theorem dom {P X c : ℝ} (pp : 1≤P) (xx : 1≤X) (big : P^100≤X)
    (cap : c≤P) (i j k l : ℕ) (budget : i<k ∧ j≤l ∨ i<100 ∧ j<l) :
    c*P^i*X^j≤P^k*X^l := by
  have pn := le_trans (by norm_num : (0:ℝ)≤1) pp
  have xn := le_trans (by norm_num : (0:ℝ)≤1) xx
  have up : c*P^i≤P^(i+1) := by rw [pow_succ,mul_comm]; gcongr
  rcases budget with ⟨ik,jl⟩|⟨ic,jl⟩
  · exact (mul_le_mul_of_nonneg_right up (pow_nonneg xn j)).trans
      (mul_le_mul (pow_le_pow_right₀ pp ik) (pow_le_pow_right₀ xx jl) (pow_nonneg xn j) (pow_nonneg pn k))
  · have room := (pow_le_pow_right₀ pp ic : P^(i+1)≤P^100).trans big
    have step := mul_le_mul_of_nonneg_right (up.trans room) (pow_nonneg xn j)
    have pay : X*X^j≤X^l := by rw [mul_comm,←pow_succ]; exact pow_le_pow_right₀ xx jl
    exact (step.trans pay).trans (le_mul_of_one_le_left (pow_nonneg xn l) (one_le_pow₀ pp))

theorem bounds {P X h E w g A D F L u : ℝ}
    (huge : 1048576≤P) (scale : P^100≤X) (tol : 1≤P*u)
    (hlo : X^10≤2*h) (hhi : h≤2*X^10) (elo : X^6≤65536*E)
    (wg : 0≤w) (gg : 0≤g) (ap : 0≤A) (dp : 0≤D) (fp : 0≤F)
    (gh : g≤h) (rows : h-g≤P^3*X^8) (width : w≤P^2*X^6)
    (coarse : F≤6*P^2*X^16) (fine : F≤L+4*(A+D)+4*g)
    (adj : A^2≤g*(A+D+6*F)) (nonedge : 2*D^2≤w^2*(4*F+D)) :
    A+D≤P^5*X^14 ∧ A≤P^3*X^13 ∧
    4*(A+D)+4*g≤u*h*E ∧
    2*h^2-2*g^2+w*(g+A)≤u*h^2 ∧ D*w^4≤u*h^4 ∧ F≤L+u*h*E := by
  have pp : 1≤P := by linarith
  have pn : 0≤P := by linarith
  have xx : 1≤X := (one_le_pow₀ pp).trans scale
  have xn : 0≤X := by linarith
  have hp : 0≤h := gg.trans gh
  have ep : 0≤E := by linarith [pow_nonneg xn 6]
  have up : 0≤u := by by_contra! neg; linarith [mul_nonpos_of_nonneg_of_nonpos pn neg.le]
  let K := P^2*X^6
  have kn : 0≤K := by dsimp [K]; positivity
  have q : 0≤P^5*X^14 := by positivity
  have gm : g≤K^2 := by
    have t := dom pp xx scale (by linarith : (2:ℝ)≤P) 0 10 4 12 (by decide)
    dsimp [K]; nlinarith only [gh,hhi,t]
  have S0 : 0≤A+D := by linarith
  have ww : w^2≤K^2 := pow_le_pow_left₀ wg width 2
  have moment : (A+D)^2≤3*K^2*((A+D)+6*F) := by
    have aa := mul_le_mul_of_nonneg_right gm (show 0≤A+D+6*F by linarith)
    have dd := mul_le_mul ww (show 4*F+D≤A+D+6*F by linarith)
      (show 0≤4*F+D by linarith) (sq_nonneg K)
    nlinarith only [aa,dd,adj,nonedge,sq_nonneg (A-D)]
  have S : A+D≤P^5*X^14 := by
    by_contra! bad
    have lin : 6*K^2≤P^5*X^14 := by
      have t := dom pp xx scale (by linarith : (6:ℝ)≤P) 4 12 5 14 (by decide)
      dsimp [K]; nlinarith only [t]
    have quad : 36*K^2*F≤(P^5*X^14)^2 := by
      have qf := mul_le_mul_of_nonneg_left coarse (show 0≤36*K^2 by positivity)
      have t := dom pp xx scale (by linarith : (216:ℝ)≤P) 6 28 10 28 (by decide)
      dsimp [K] at *; nlinarith only [qf,t]
    have f1 := mul_le_mul_of_nonneg_right (lin.trans bad.le) S0
    have f2 := pow_lt_pow_left₀ bad q (by decide : 2≠0)
    nlinarith only [moment,f1,f2,quad]
  have ab : A≤P^3*X^13 := by
    have sm := dom pp xx scale (by linarith : (1:ℝ)≤P) 5 14 2 16 (by decide)
    have mass : A+D+6*F≤37*P^2*X^16 := by nlinarith only [sm,S,coarse]
    have prod := mul_le_mul (gh.trans hhi) mass (show 0≤A+D+6*F by linarith) (by positivity)
    have t := dom pp xx scale (by linarith : (74:ℝ)≤P) 2 26 6 26 (by decide)
    by_contra! bad
    have sq := pow_lt_pow_left₀ bad (show 0≤P^3*X^13 by positivity) (by decide : 2≠0)
    nlinarith only [sq,t,prod,adj]
  have he := mul_le_mul hlo elo (pow_nonneg xn 6) (by linarith : 0≤2*h)
  have cost : 4*(A+D)+4*g≤u*h*E := by
    have t := dom pp xx scale (by linarith : (1048576:ℝ)≤P) 6 14 0 16 (by decide)
    have v := dom pp xx scale (by linarith : (16:ℝ)≤P) 0 10 5 14 (by decide)
    have sg : 4*(A+D)+4*g≤8*P^5*X^14 := by nlinarith only [S,gh,hhi,v,pow_nonneg xn 10]
    have hi := mul_le_mul_of_nonneg_left sg pn
    have pay := mul_le_mul_of_nonneg_right tol (mul_nonneg hp ep)
    by_contra! bad
    have strict := mul_lt_mul_of_pos_left bad (by linarith : 0<P)
    nlinarith only [hi,pay,t,he,strict]
  have row : 2*h^2-2*g^2+w*(g+A)≤u*h^2 := by
    have deficit := mul_le_mul rows (show h+g≤4*X^10 by linarith) (by linarith : 0≤h+g)
      (show 0≤P^3*X^8 by positivity)
    have mix := mul_le_mul width (show g+A≤2*X^10+P^3*X^13 by linarith)
      (by linarith : 0≤g+A) (show 0≤P^2*X^6 by positivity)
    have cut : 2*h^2-2*g^2+w*(g+A) ≤ 8*P^3*X^18+2*P^2*X^16+P^5*X^19 := by
      nlinarith only [deficit,mix]
    have t1 := dom pp xx scale (by linarith : (96:ℝ)≤P) 4 18 0 20 (by decide)
    have t2 := dom pp xx scale (by linarith : (24:ℝ)≤P) 3 16 0 20 (by decide)
    have t3 := dom pp xx scale (by linarith : (12:ℝ)≤P) 6 19 0 20 (by decide)
    have pay := mul_le_mul_of_nonneg_right tol (sq_nonneg h)
    have base := pow_le_pow_left₀ (pow_nonneg xn 10) hlo 2
    have bound := mul_le_mul_of_nonneg_left cut pn
    by_contra! bad
    have strict := mul_lt_mul_of_pos_left bad (by linarith : 0<P)
    nlinarith only [strict,bound,pay,base,t1,t2,t3]
  have dia : D*w^4≤u*h^4 := by
    have dcap : D≤P^5*X^14 := by linarith
    have dw := mul_le_mul dcap (pow_le_pow_left₀ wg width 4) (pow_nonneg wg 4) q
    have t1 := dom pp xx scale (by linarith : (16:ℝ)≤P) 14 38 0 40 (by decide)
    have base := pow_le_pow_left₀ (pow_nonneg xn 10) hlo 4
    have bound := mul_le_mul_of_nonneg_left dw pn
    have pay := mul_le_mul_of_nonneg_right tol (pow_nonneg hp 4)
    by_contra! bad
    have strict := mul_lt_mul_of_pos_left bad (by linarith : 0<P)
    nlinarith only [strict,bound,pay,base,t1]
  exact ⟨S,ab,cost,row,dia,by linarith⟩

#print axioms bounds
end ThresholdUniformGraphErrors
