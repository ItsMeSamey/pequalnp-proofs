import ExactPlaneWedgeCodec
namespace ExactPlaneWedgeCodecCorrect
open ExactPlaneWedgeCodec ExactPlaneWedgeProduct ExactPlaneWedgeSplit ExactPlaneWedgeBoundary
variable {d a b c : ℕ}
abbrev K (d : ℕ) := Word d

theorem compatible_iff (L R E : Submodule F (K d))
    (A : Fin a → Word d) (B : Fin b → Word d) (C : Fin c → Word d)
    (ea : Word a ≃ₗ[F] leftBoundary L R E) (eb : Word b ≃ₗ[F] rightBoundary L R E)
    (ec : Word c ≃ₗ[F] parentBoundary L R E)
    (ha : ∀x, image A x = (ea x).val) (hb : ∀x, image B x = (eb x).val)
    (hc : ∀x, image C x = (ec x).val)
    (l : Code a) (r : Code b) (s : Code c)
    (ls : State (leftBoundary L R E) (F×F)) (rs : State (rightBoundary L R E) (F×F))
    (ss : State (parentBoundary L R E) (F×F))
    (lp : ea l.p=ls.p) (lq : ea l.q=ls.q) (rp : eb r.p=rs.p) (rq : eb r.q=rs.q)
    (sp : ec s.p=ss.p) (sq : ec s.q=ss.q)
    (lg : ∀x, gamma l x=ls.chart (ea x)) (rg : ∀x,gamma r x=rs.chart (eb x))
    (sg : ∀x,gamma s x=ss.chart (ec x)) :
    compatible A B C l r s=true ↔ Compatible L R E ss ls rs := by
  simp only [compatible,Bool.and_eq_true,decide_eq_true_eq,List.all_eq_true,
    ExactPlaneNumericalRows.mem_words,true_implies,ha,hb,hc,lp,lq,rp,rq,sp,sq,lg,rg,sg]
  constructor
  · rintro ⟨⟨p,q⟩,all⟩
    have outer (u : leftBoundary L R E) (v : rightBoundary L R E) (w : parentBoundary L R E)
        (h : (u:K d)+(v:K d)=w) : ls.chart u+rs.chart v=ss.chart w := by
      have H := all (ea.symm u) (eb.symm v) (ec.symm w)
      simpa using H (by simpa using h)
    refine ⟨p,q,?_,outer⟩
    intro x
    let u : leftBoundary L R E := ⟨x.val,overlap_left L R E x.property⟩
    let v : rightBoundary L R E := ⟨x.val,overlap_right L R E x.property⟩
    have h := outer u (-v) 0 (by change x.val + -x.val=0; simp)
    change ls.chart u=rs.chart v
    apply sub_eq_zero.mp
    simpa [sub_eq_add_neg] using h
  · intro ok
    exact ⟨⟨ok.p,ok.q⟩,fun x y z => ok.outer (ea x) (eb y) (ec z)⟩
end ExactPlaneWedgeCodecCorrect
