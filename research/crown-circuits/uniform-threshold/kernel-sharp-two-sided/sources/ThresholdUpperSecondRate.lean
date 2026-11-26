import ThresholdUpperRateInterface
import ThresholdUpperScalarRate
import ThresholdSharpNatTally
namespace ThresholdUpperSecondRate
open ThresholdUpperSecond ThresholdUpperActualSelection ThresholdUpperInjection
private theorem splitting (Z j k : Nat) :
    Z.descFactorial (j+k)=Z.descFactorial j*(Z-j).descFactorial k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.add_succ,Nat.descFactorial_succ,Nat.descFactorial_succ,ih,Nat.sub_sub]
    ring

private theorem cost_eq (w z q : Nat) (enough : 4+q≤w) :
    pairCost w z q*(Fintype.card (Edges z)-4).descFactorial q=
      Fintype.card (Injection w z)*partitionCount q (2*q) := by
  let Z := Fintype.card (Edges z)
  have j : w=4+(q+(w-4-q)) := by omega
  have denom : Fintype.card (Injection w z)=Z.descFactorial 4*
      ((Z-4).descFactorial q*(Z-4-q).descFactorial (w-4-q)) := by
    simp only [Injection,Fintype.card_embedding_eq,Fintype.card_fin]
    change Z.descFactorial w=_
    conv_lhs => rw [j,splitting,splitting (Z-4) q]
  rw [denom]
  unfold pairCost
  dsimp only [Z]
  ring

private theorem fail_eq (w z : Nat) (enough : 2≤w) :
    failCost w z*(Fintype.card (Edges z)-1)=12*(z-2)*Fintype.card (Injection w z) := by
  let Z := Fintype.card (Edges z)
  have den : Fintype.card (Injection w z)=Z*(Z-1)*(Z-2).descFactorial (w-2) := by
    simp only [Injection,Fintype.card_embedding_eq,Fintype.card_fin]
    change Z.descFactorial w=_
    conv_lhs => rw [show w=2+(w-2) by omega,splitting]
    simp [Nat.descFactorial_succ,Nat.mul_comm]
  rw [den]; unfold failCost; dsimp only [Z]; ring

private theorem denominator {y : ℝ} {Z z : Nat} (large : 10≤z)
    (zz : 2*(Z:ℝ)=(z:ℝ)*(z-1:ℝ)) (yn : 0≤y) (floor : y^45≤z)
    (q : Nat) (hq : q≤4) :
    (y^90)^q≤4^q*(((Z-4).descFactorial q:Nat):ℝ) := by
  have z0 : (10:ℝ)≤z := by exact_mod_cast large
  have y0 := pow_nonneg yn 45
  have sq := pow_le_pow_left₀ y0 floor 2
  have room : (z:ℝ)^2≤4*((Z:ℝ)-7) := by nlinarith only [zz,z0,sq_nonneg ((z:ℝ)-5)]
  have Z7 : 7≤Z := by
    have : (7:ℝ)≤Z := by nlinarith [sq_nonneg (z:ℝ)]
    exact_mod_cast this
  induction q with
  | zero => simp
  | succ q ih =>
    have q3 : q≤3 := by omega
    have cut : q≤Z-4 := by omega
    have cast : ((Z-4-q:Nat):ℝ)=(Z:ℝ)-4-q := by rw [Nat.cast_sub cut,Nat.cast_sub (by omega : 4≤Z)]; norm_num
    have qR : (q:ℝ)≤3 := by exact_mod_cast q3
    have factor : y^90≤4*((Z-4-q:Nat):ℝ) := by rw [cast]; nlinarith only [room,sq,qR]
    have product := mul_le_mul (ih (by omega)) factor (by positivity) (by positivity)
    rw [pow_succ,pow_succ (4:ℝ),Nat.descFactorial_succ,Nat.cast_mul]
    nlinarith only [product]

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1400000 in
theorem second_rate : ThresholdUpperParameters.SecondRate := by
  intro y n v w z k ybig vy wl wh zl zh kl kh
  let Z := Fintype.card (Edges z)
  let J := Fintype.card (Injection w z)
  let fc : ℝ := failCost w z
  let cost := fun q : Nat => (pairCost w z q:ℝ)
  have y1 : 1≤y := by linarith only [ybig]
  have yp : 0<y := by linarith only [ybig]
  have yn := yp.le
  have pow_growth : ∀ exponent : Nat, 1 ≤ exponent → y ≤ y ^ exponent := by
    intro exponent hexp
    simpa only [pow_one] using pow_le_pow_right₀ y1 hexp
  have giantZ : 10≤z := by
    have : (10:ℝ)≤z := by linarith only [pow_growth 45 (by decide),zl,ybig]
    exact_mod_cast this
  have giantW : 8≤w := by
    have : (8:ℝ)≤w := by linarith only [pow_growth 60 (by decide),wl,ybig]
    exact_mod_cast this
  have Zsize : Z=z.choose 2 := by simp [Z,Edges,Finset.card_powersetCard]
  have zz : 2*(Z:ℝ)=(z:ℝ)*(z-1:ℝ) := by rw [Zsize]; exact_mod_cast ThresholdSharpArithmetic.twice_choose_two z
  have y30 := pow_growth 30 (by decide)
  have sq := pow_le_pow_left₀ (pow_nonneg yn 45) zl 2
  have enough : (w:ℝ)≤Z := by
    have grow := mul_le_mul_of_nonneg_right (show 12≤y^30 by linarith only [ybig,y30]) (pow_nonneg yn 60)
    have zlarge : (10:ℝ)≤z := by exact_mod_cast giantZ
    have prod := mul_nonneg (show 0≤(z:ℝ)-2 by linarith) (Nat.cast_nonneg z : (0:ℝ)≤z)
    nlinarith only [grow,wh,zz,sq,prod]
  refine ⟨by exact_mod_cast enough,?_⟩
  intro f cap allowance
  have fail : fc*y^45≤24*(J:ℝ) := by
    have eq := fail_eq w z (by omega)
    change failCost w z*(Z-1)=12*(z-2)*J at eq
    have z10 : (10:ℝ)≤z := by exact_mod_cast giantZ
    have z3 : 3≤Z := by
      have : (3:ℝ)≤Z := by nlinarith only [zz,z10,sq_nonneg ((z:ℝ)-3)]
      exact_mod_cast this
    have hEq : fc*((Z:ℝ)-1)=12*((z:ℝ)-2)*J := by
      dsimp only [fc]; exact_mod_cast (show (failCost w z:ℝ)*((Z:ℝ)-1)=12*((z:ℝ)-2)*J by
        simpa only [Nat.cast_mul,Nat.cast_sub (by omega : 1≤Z),Nat.cast_sub (by omega : 2≤z),Nat.cast_one,Nat.cast_ofNat] using congrArg (fun x : Nat => (x:ℝ)) eq)
    have cancel : (z:ℝ)*((z:ℝ)-2)≤2*((Z:ℝ)-1) := by nlinarith only [zz,z10]
    have left := mul_le_mul_of_nonneg_left zl (show 0≤fc by dsimp [fc]; positivity)
    have mult := mul_le_mul_of_nonneg_right cancel (show 0≤12*(J:ℝ) by positivity)
    have hmult := congrArg (fun t : ℝ => t*(z:ℝ)) hEq
    have z3R : (3:ℝ)≤Z := by exact_mod_cast z3
    have zzpos : 0<(Z:ℝ)-1 := by linarith only [z3R]
    apply (le_of_mul_le_mul_right ?_ zzpos)
    have zz1 := zzpos.le
    have mono := mul_le_mul_of_nonneg_right left zz1
    nlinarith only [hmult,mult,mono]
  have price (q : Nat) (hq : q≤4) : cost q*(y^90)^q≤(4:ℝ)^q*partitionCount q (2*q)*J := by
    have d := denominator giantZ zz yn zl q hq
    have exactN := cost_eq w z q (by omega)
    change pairCost w z q*(Z-4).descFactorial q=J*partitionCount q (2*q) at exactN
    have cast : cost q*((Z-4).descFactorial q:ℝ)=(J:ℝ)*partitionCount q (2*q) := by dsimp only [cost]; exact_mod_cast exactN
    have scaled := congrArg (fun r : ℝ => (4:ℝ)^q*r) cast
    have dl := mul_le_mul_of_nonneg_left d (show 0≤cost q by dsimp [cost]; positivity)
    nlinarith only [dl,scaled]
  obtain ⟨c2,c3,c4⟩ := collision_constants
  have p2 := price 2 (by decide)
  have p3 := price 3 (by decide)
  have p4 := price 4 (by decide)
  norm_num [c2,c3,c4] at p2 p3 p4
  have f2 : 2*(f:ℝ)≤y^200 := by
    have eq : 2*((v.choose 2:Nat):ℝ)=(v:ℝ)*(v-1:ℝ) := by exact_mod_cast ThresholdSharpArithmetic.twice_choose_two v
    have le : (f:ℝ)≤v.choose 2 := by exact_mod_cast cap
    rw [←vy] at eq
    nlinarith only [le,eq,pow_nonneg yn 100]
  have k0 : 1≤k := by
    have : (1:ℝ)≤k := (one_le_pow₀ y1).trans kl
    exact_mod_cast this
  have dd : ((v+(k-1)^2-1:Nat):ℝ)≤2*y^100 := by
    have small : (k-1:ℝ)≤y^50 := by linarith only [kh]
    have non : 0≤(k:ℝ)-1 := sub_nonneg.mpr (by exact_mod_cast k0)
    have sq := pow_le_pow_left₀ non small 2
    have sub := Nat.sub_le (v+(k-1)^2) 1
    have z : ((v+(k-1)^2-1:Nat):ℝ)≤(v:ℝ)+((k:ℝ)-1)^2 := by
      have qr : ((v+(k-1)^2-1:Nat):ℝ)≤((v+(k-1)^2:Nat):ℝ) := by exact_mod_cast sub
      simpa only [Nat.cast_add,Nat.cast_pow,Nat.cast_sub k0,Nat.cast_one] using qr
    nlinarith only [z,sq,vy]
  have count2 : ((3*f*(v+(k-1)^2-1):Nat):ℝ)≤3*y^300 := by
    push_cast
    nlinarith only [mul_le_mul f2 dd (Nat.cast_nonneg _) (pow_nonneg yn 200)]
  have fc2 : ((f.choose 2:Nat):ℝ)≤y^400 := by
    have eq : 2*((f.choose 2:Nat):ℝ)=(f:ℝ)*(f-1:ℝ) := by exact_mod_cast ThresholdSharpArithmetic.twice_choose_two f
    have fs := pow_le_pow_left₀ (show 0≤2*(f:ℝ) by positivity) f2 2
    nlinarith only [eq,fs,(Nat.cast_nonneg (f.choose 2) : (0:ℝ)≤f.choose 2),(Nat.cast_nonneg f : (0:ℝ)≤f)]
  have fa : (f:ℝ)*fc≤12*y^155*J := by
    apply (le_of_mul_le_mul_right ?_ (pow_pos yp 45))
    nlinarith only [mul_le_mul f2 fail (show 0≤fc*y^45 by dsimp [fc]; positivity) (pow_nonneg yn 200)]
  let b := 3*f*(v+(k-1)^2-1)
  have bb : (b:ℝ)*cost 2≤1000000*y^120*J := by
    apply (le_of_mul_le_mul_right ?_ (pow_pos yp 180))
    have prod := mul_le_mul count2 p2 (show 0≤cost 2*(y^90)^2 by dsimp [cost]; positivity) (show 0≤3*y^300 by positivity)
    dsimp only [b]
    nlinarith only [prod,mul_nonneg (pow_nonneg yn 300) (Nat.cast_nonneg J : (0:ℝ)≤J)]
  let m := max (pairCost w z 3) (pairCost w z 4)
  have pm : (m:ℝ)*y^270≤645120*J := by
    have ord := pow_le_pow_right₀ y1 (by decide : 270≤360)
    dsimp only [m]
    by_cases h : pairCost w z 3≤pairCost w z 4
    · rw [max_eq_right h]
      have lowered := mul_le_mul_of_nonneg_left ord (show 0≤cost 4 by dsimp [cost]; positivity)
      change cost 4*y^270≤_
      nlinarith only [p4,lowered]
    · rw [max_eq_left (by omega)]
      change cost 3*y^270≤_
      nlinarith only [p3,(Nat.cast_nonneg J : (0:ℝ)≤J)]
  have cc : ((f.choose 2:Nat):ℝ)*m≤2000000*y^130*J := by
    apply (le_of_mul_le_mul_right ?_ (pow_pos yp 270))
    have prod := mul_le_mul fc2 pm (show 0≤(m:ℝ)*y^270 by positivity) (pow_nonneg yn 400)
    nlinarith only [prod,mul_nonneg (pow_nonneg yn 400) (Nat.cast_nonneg J : (0:ℝ)≤J)]
  have o1 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ y1 (by decide : 120≤155)) (Nat.cast_nonneg J : (0:ℝ)≤J)
  have o2 := mul_le_mul_of_nonneg_right (pow_le_pow_right₀ y1 (by decide : 130≤155)) (Nat.cast_nonneg J : (0:ℝ)≤J)
  have fund := mul_le_mul_of_nonneg_right allowance (Nat.cast_nonneg J : (0:ℝ)≤J)
  change J*n+f*failCost w z+b*pairCost w z 2+f.choose 2*m≤J*f
  have final : (J:ℝ)*n+(f:ℝ)*fc+(b:ℝ)*cost 2+((f.choose 2:Nat):ℝ)*m≤(J:ℝ)*f := by
    nlinarith only [fa,bb,cc,o1,o2,fund,mul_nonneg (pow_nonneg yn 155) (Nat.cast_nonneg J : (0:ℝ)≤J)]
  dsimp only [fc,cost] at final
  exact_mod_cast final
#print axioms second_rate
end ThresholdUpperSecondRate
