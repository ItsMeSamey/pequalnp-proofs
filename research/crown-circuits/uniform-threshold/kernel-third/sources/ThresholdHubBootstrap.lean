import ThresholdHubDeficits
namespace ThresholdHubBootstrap

/-- Doubled form of q≤K. Q is the number of strict comparable pairs; m is
the number of shared raw edges. The equality defining q is indispensable. -/
theorem incomparable_deficit {s n h d e b m P q : ℤ} (h0 : 0≤h) (d0 : 0≤d)
    (fund : h+d≤s+1) (avoid : e≤4) (classes : n=e+m+b)
    (leaves : b≤3*h+P+h*d) (missing : 2*(m+P+q)=h*(h-1)) :
    2*q ≤ s^2+7*s+14-2*n := by
  have gap := mul_nonneg (show 0≤s+1-h by omega) (show 0≤s+6-h by omega)
  have pay := mul_le_mul_of_nonneg_left (show d≤s+1-h by omega) h0
  nlinarith only [fund,avoid,classes,leaves,missing,gap,pay]

/-- Rough relative density supplies 4*l≤h. The improvement uses two ideal
cuts of at most B each and the exact unordered-pair capacity among low hubs. -/
theorem improve {h l M q B : ℤ} (l0 : 0≤l) (rough : 4*l≤h)
    (missing : 2*M≤2*q+4*B+l*(l-1)) (low : l*(h-2)≤4*M) :
    l*h≤8*q+16*B := by
  have pay := mul_nonneg l0 (show 0≤h-4*l by omega)
  nlinarith only [missing,low,pay]

/-- For h≥4, M≤h²/32 implies at most a quarter of the hubs are low. -/
theorem initiate {h l M : ℤ} (hh : 4≤h) (l0 : 0≤l)
    (rough : 32*M≤h*h) (low : l*(h-2)≤4*M) : 4*l≤h := by
  by_contra! large
  have same := mul_pos (show 0<4*l-h by omega) (show 0<h-2 by omega)
  have correction := mul_nonneg (show 0≤h by omega) (show 0≤h-4 by omega)
  nlinarith only [same,low,rough,correction]

/-- Once the low count is bounded, return to incidence rather than paying the
full quadratic low-low term: it is at most l*h/8 in the quarter regime. -/
theorem refined_missing {h l M q B : ℤ} (l0 : 0≤l) (rough : 4*l≤h)
    (missing : 2*M≤2*q+4*B+l*(l-1)) (low : l*(h-2)≤4*M) :
    M≤2*q+4*B := by
  have cap := improve l0 rough missing low
  have rem := mul_nonneg l0 (show 0≤h-4*l by omega)
  nlinarith only [missing,cap,rem,l0]

/-- AND-count consequence in an entirely division-free form, without assuming
a positive gap s−sqrt(2n). The connected-component/probe bookkeeping feeds
handshake, degree and components below. -/
theorem and_budget {s t n h a Δ c e m M low : ℝ} (h0 : 0≤h) (square : t^2=2*n)
    (avoid : e≤4) (fullPairs : 2*(m+M)=h*(h-1))
    (handshake : n-e+m≤h*Δ) (degree : a+Δ≤s+4+c)
    (components : c≤low+5) :
    a*h ≤ (s-t)*h + (low+19/2)*h + M + 4 := by
  have gd := mul_le_mul_of_nonneg_right degree h0
  have cc := mul_le_mul_of_nonneg_right components h0
  nlinarith only [square,avoid,fullPairs,handshake,gd,cc,sq_nonneg (h-t)]
#print axioms improve
#print axioms and_budget
end ThresholdHubBootstrap
