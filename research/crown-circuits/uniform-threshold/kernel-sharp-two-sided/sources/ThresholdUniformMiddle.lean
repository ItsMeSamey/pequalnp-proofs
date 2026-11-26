import ThresholdNativeSharpColumnLedger
import Mathlib.Tactic.Positivity
namespace ThresholdUniformMiddle

/-- Z=P X^8, Y=P² X^6. Only X²≥100P is needed in this stage. -/
theorem scales {P X : ℝ} (p : 100≤P) (x : 1≤X) (room : 100*P≤X^2) :
    1≤P*X^8 ∧ P^2*X^6≤P*X^8 ∧ 100*(P*X^8)≤X^10 := by
  have x8 : 1≤X^8 := one_le_pow₀ x
  have px := mul_nonneg (show 0≤P by linarith) (sub_nonneg.mpr (show P≤X^2 by linarith))
  have y := mul_nonneg px (show 0≤X^6 by positivity)
  have r := mul_le_mul_of_nonneg_right room (show 0≤X^8 by positivity)
  have z := mul_le_mul_of_nonneg_right (show 1≤P by linarith) (show 0≤X^8 by positivity)
  constructor
  · linarith
  constructor <;> nlinarith only [y,r]

theorem trim_and_space {P X h low H M T μ : ℝ} (p : 100≤P) (x : 1≤X)
    (scale : 100*P≤X^2) (lo : X^10≤2*h) (hi : h≤2*X^10)
    (lowCap : low≤P^2*X^6) (part : H+low=h) (mCap : M≤P^2*X^16)
    (trim : T≤2*M+h+2*h*low) (floor : μ^2≤T) :
    T≤8*P^2*X^16 ∧ μ≤3*P*X^8 ∧ 9*T<H^2 ∧ 2*(low+2*μ+1)≤h ∧ low+4*μ≤h := by
  obtain ⟨z,y,r⟩ := scales p x scale
  have h0 : 0≤h := by linarith
  have Y0 : 0≤P^2*X^6 := by positivity
  have many := (mul_le_mul_of_nonneg_left lowCap h0).trans (mul_le_mul_of_nonneg_right hi Y0)
  have x6 : 1≤X^6 := one_le_pow₀ x
  have psq : 1≤P^2 := by nlinarith
  have px := mul_le_mul x6 psq (by positivity) (by positivity)
  have tt := mul_le_mul_of_nonneg_left px (show 0≤X^10 by positivity)
  have cap : T≤8*P^2*X^16 := by nlinarith only [trim,mCap,hi,many,tt]
  have muCap : μ≤3*P*X^8 := by
    by_contra! gt
    have prod := mul_pos (sub_pos.mpr gt) (show 0<μ+3*P*X^8 by linarith)
    nlinarith only [prod,floor,cap,sq_nonneg (P*X^8)]
  have high : 40*(P*X^8)≤H := by linarith
  have gap := mul_nonneg (sub_nonneg.mpr high) (show 0≤H+40*(P*X^8) by linarith)
  have pos := mul_pos (show 0<P*X^8 by linarith) (show 0<P*X^8 by linarith)
  exact ⟨cap,muCap,by nlinarith only [gap,cap,pos],by linarith,by linarith⟩

theorem private_count {P X M j : ℝ} (z : 1≤P*X^8) (mCap : M≤P^2*X^16)
    (choose : j*(j-1)≤2*(M+1)) : j≤3*P*X^8 := by
  by_contra! gt
  have prod := mul_pos (sub_pos.mpr gt) (show 0<j+3*P*X^8-1 by linarith)
  have sq := mul_nonneg (show 0≤P*X^8-1 by linarith) (show 0≤P*X^8 by linarith)
  nlinarith only [prod,choose,mCap,sq,z]

theorem impurity {P X h E K I a low : ℝ} (p : 8≤P) (x : 0≤X) (h0 : 0<h)
    (kCap : 2*K≤4*X^10*E) (lo : X^10≤2*h) (e0 : 0≤E) (eCap : E≤P*X^6)
    (aCap : a≤P^2*X^6) (lCap : low≤P^2*X^6)
    (ledger : h*I≤2*K+h*(5*a+2*low-2)) : I≤8*P^2*X^6 := by
  have tt := mul_le_mul_of_nonneg_right lo (show 0≤4*E by positivity)
  have scale := mul_nonneg (show 0≤P by linarith) (show 0≤P-8 by linarith)
  have ee := mul_le_mul_of_nonneg_right scale (show 0≤X^6 by positivity)
  have bound : 8*E+5*a+2*low-2≤8*P^2*X^6 := by nlinarith only [ee,eCap,aCap,lCap]
  have prop := mul_le_mul_of_nonneg_left bound h0.le
  apply (le_of_mul_le_mul_left ?_ h0)
  nlinarith only [prop,ledger,kCap,tt]

theorem row_error {P X h g low imp δ a j μ V : ℝ} (p : 100≤P)
    (z : 1≤P*X^8) (yx : P^2*X^6≤P*X^8) (gCap : g≤h)
    (ledger : h≤g+low+imp+δ+3*a+4*j+μ+2*V)
    (lCap : low≤P^2*X^6) (iCap : imp≤8*P^2*X^6) (dCap : δ≤4*P*X^8)
    (aCap : a≤P^2*X^6) (jCap : j≤3*P*X^8) (muCap : μ≤3*P*X^8)
    (vCap : V≤P^2*X^6) : |h-g|≤P^3*X^8 := by
  rw [abs_of_nonneg (sub_nonneg.mpr gCap)]
  have big := mul_nonneg (show 0≤P^2-40 by nlinarith) (show 0≤P*X^8 by linarith)
  nlinarith only [ledger,lCap,iCap,dCap,aCap,jCap,muCap,vCap,big,yx,z]

theorem col_error {P X h E K L w low μ : ℝ} (p : 2^20≤P) (x : 0<X) (h0 : 0<h) (e0 : 0<E)
    (lo : X^10≤2*h) (lowCap : low≤P^2*X^6) (muCap : μ≤3*P*X^8)
    (scale : P^2*X^6≤P*X^8) (w0 : 0≤w) (cap : w≤65536*P^2*E)
    (near : K/(h*E)≤1+20*P^2/X^2)
    (ledger : (h-low-4*μ)*w+L≤K) :
    w/E≤1-L/(h*E)+P^6/X^2 := by
  have x2 : 0<X^2 := by positivity
  have he : 0<h*E := by positivity
  have k := (div_le_iff₀ he).mp near
  have k' : K*X^2≤(X^2+20*P^2)*(h*E) := calc
    _ ≤ ((1+20*P^2/X^2)*(h*E))*X^2 := mul_le_mul_of_nonneg_right k x2.le
    _ = _ := by field_simp <;> ring
  have debit := mul_le_mul_of_nonneg_right (show low+4*μ≤13*P*X^8 by linarith) w0
  have wc := mul_le_mul_of_nonneg_left cap (show 0≤13*P*X^8 by positivity)
  have dx := mul_le_mul_of_nonneg_right (debit.trans wc) x2.le
  have hh := mul_le_mul_of_nonneg_right lo (show 0≤851968*P^3*E by positivity)
  have coeff : 20*P^2+1703936*P^3≤P^6 := by
    have pp : 2≤P := by linarith
    have p3 : 2*P≤P^2 := by nlinarith [mul_nonneg (show 0≤P by linarith) (show 0≤P-2 by linarith)]
    have big : 1703956≤P^3 := by nlinarith [mul_nonneg (show 0≤P^2-2 by nlinarith) (show 0≤P-1 by linarith)]
    have fin := mul_le_mul_of_nonneg_right big (show 0≤P^3 by positivity)
    nlinarith only [fin,p3,mul_nonneg (show 0≤P^2 by positivity) (show 0≤P-1 by linarith)]
  have margin := mul_le_mul_of_nonneg_right coeff he.le
  have pay := mul_le_mul_of_nonneg_right ledger x2.le
  field_simp [ne_of_gt h0,ne_of_gt e0,ne_of_gt x2]
  nlinarith only [pay,k',dx,hh,margin]
theorem nat_room {P X : ℝ} {h H low M T : Nat} (p : 100≤P) (x : 1≤X)
    (scale : 100*P≤X^2) (lo : X^10≤2*(h:ℝ)) (hi : (h:ℝ)≤2*X^10)
    (lowCap : (low:ℝ)≤P^2*X^6) (part : H+low=h) (mCap : (M:ℝ)≤P^2*X^16)
    (trim : T≤2*M+h+2*h*low) :
    (T.sqrt:ℝ)≤3*P*X^8 ∧ 9*T<H^2 ∧ 2*(low+2*T.sqrt+1)≤h ∧ low+4*T.sqrt≤h := by
  have floor : T.sqrt^2≤T := by simpa [pow_two] using Nat.sqrt_le T
  obtain ⟨_,mu,r,s,z⟩ := trim_and_space p x scale lo hi lowCap
    (by exact_mod_cast part : (H:ℝ)+(low:ℝ)=(h:ℝ)) mCap
    (by exact_mod_cast trim : (T:ℝ)≤2*(M:ℝ)+(h:ℝ)+2*(h:ℝ)*(low:ℝ))
    (by exact_mod_cast floor : (T.sqrt:ℝ)^2≤(T:ℝ))
  exact ⟨mu,by exact_mod_cast r,by exact_mod_cast s,by exact_mod_cast z⟩

#print axioms nat_room
#print axioms row_error
#print axioms col_error
end ThresholdUniformMiddle
