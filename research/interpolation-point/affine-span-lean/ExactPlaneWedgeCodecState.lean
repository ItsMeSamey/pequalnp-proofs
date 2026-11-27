import ExactPlaneWedgeCodecCorrect
namespace ExactPlaneWedgeCodecState
open ExactPlaneWedgeCodec ExactPlaneWedgeSplit ExactPlaneWedgeProduct
open scoped BigOperators
variable {r d : ℕ} {J : Submodule F (Word d)}
def chartLinear (s : Code r) : Word r →ₗ[F] (F×F) where
  toFun := gamma s
  map_add' := by intro x y; apply Prod.ext <;> simp [gamma,add_mul,Finset.sum_add_distrib]
  map_smul' := by intro c x; apply Prod.ext <;> simp [gamma,mul_assoc,Finset.mul_sum]
def decode (e : Word r ≃ₗ[F] J) (s : Code r) : State J (F×F) :=
  ⟨(chartLinear s).comp e.symm.toLinearMap,e s.p,e s.q⟩
def encode (e : Word r ≃ₗ[F] J) (s : State J (F×F)) : Code r :=
  ⟨fun i => (s.chart (e (Pi.single i 1))).1,fun i => (s.chart (e (Pi.single i 1))).2,
    e.symm s.p,e.symm s.q⟩
theorem gamma_encode (e : Word r ≃ₗ[F] J) (s : State J (F×F)) (x : Word r) :
    gamma (encode e s) x=s.chart (e x) := by
  have expand : (∑ i, x i • (Pi.single i 1 : Word r))=x := by
    funext j
    simp [Finset.sum_apply,Pi.single_apply]
  have h := congrArg (fun z => s.chart (e z)) expand
  simp only [map_sum,map_smul] at h
  apply Prod.ext
  · simpa [gamma,encode,Prod.fst_sum,smul_eq_mul] using congrArg Prod.fst h
  · simpa [gamma,encode,Prod.snd_sum,smul_eq_mul] using congrArg Prod.snd h
theorem gamma_decode (e : Word r ≃ₗ[F] J) (s : Code r) (x : Word r) :
    (decode e s).chart (e x)=gamma s x := by simp [decode,chartLinear]
theorem decode_encode (e : Word r ≃ₗ[F] J) (s : State J (F×F)) :
    decode e (encode e s)=s := by
  have hc : (decode e (encode e s)).chart=s.chart := by
    apply LinearMap.ext
    intro x
    obtain ⟨u,rfl⟩ := e.surjective x
    rw [gamma_decode,gamma_encode]
  have hp : (decode e (encode e s)).p=s.p := e.apply_symm_apply _
  have hq : (decode e (encode e s)).q=s.q := e.apply_symm_apply _
  generalize hz : decode e (encode e s)=z at *
  cases s
  cases z
  simp_all
theorem decode_surjective (e : Word r ≃ₗ[F] J) : Function.Surjective (decode e) :=
  fun s => ⟨encode e s,decode_encode e s⟩

open ExactPlaneWedgeBoundary
theorem compatible_decoded {a b c : ℕ} (L R E : Submodule F (Word d))
    (A : Fin a → Word d) (B : Fin b → Word d) (C : Fin c → Word d)
    (ea : Word a ≃ₗ[F] leftBoundary L R E) (eb : Word b ≃ₗ[F] rightBoundary L R E)
    (ec : Word c ≃ₗ[F] parentBoundary L R E)
    (ha : ∀x, image A x=(ea x).val) (hb : ∀x,image B x=(eb x).val)
    (hc : ∀x,image C x=(ec x).val) (l : Code a) (r : Code b) (s : Code c) :
    compatible A B C l r s=true ↔ Compatible L R E (decode ec s) (decode ea l) (decode eb r) :=
  ExactPlaneWedgeCodecCorrect.compatible_iff L R E A B C ea eb ec ha hb hc l r s
    _ _ _ rfl rfl rfl rfl rfl rfl (fun x => (gamma_decode ea l x).symm)
    (fun x => (gamma_decode eb r x).symm) (fun x => (gamma_decode ec s x).symm)

end ExactPlaneWedgeCodecState
