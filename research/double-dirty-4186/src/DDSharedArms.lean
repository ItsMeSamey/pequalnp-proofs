import DDFactorOriginal
import DDFactorAbsorption
import Q1DoubleTopology
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.MetaComplexity.NestedCover
open PEqualNP.EdgeOwnership PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0.Factor S4183.S98
attribute [local instance] PEqualNP.MetaComplexity.NestedCover.gateOpDecEq

theorem live_dirty {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (C : Circuit) (g : ℕ)
    (hg : g < C.gates.length) (dirty : ¬ BelowF G C g) (edge : G.edgeFinset.Nonempty)
    (least : IsLeastAO G C) : ∃ t ∈ tops G C, Influence n C g (n+t) := by
  have hf : ∀ x : Fin n → Bool, C.eval (List.ofFn x) = graphFun G ∅ x := fun x => congrFun least.2.1 x
  have hL : Least n C := ⟨AO_of_IsAO2 n C least.1, fun D hD agree =>
    least.2.2 D (IsAO2_of_AO n D hD) (funext fun x => (agree x).trans (hf x))⟩
  obtain ⟨_,hout⟩ := least_out n C hL
    (by obtain ⟨x,hx⟩ := gf_true n G edge; exact ⟨x,(hf x).trans hx⟩)
    (by intro u; obtain ⟨x,hu,hx⟩ := gf_var n G u; exact ⟨x,hu,(hf x).trans hx⟩)
  have go (k : ℕ) : ∀ i < C.gates.length, C.gates.length-i=k → ¬ BelowF G C i →
      Influence n C g (n+i) → ∃ t ∈ tops G C, Influence n C g (n+t) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro i hi eq bad path
      have ne : n+i ≠ C.output := by
        rintro wire
        apply bad
        intro x hv
        change W n C x (n+i) = true at hv
        rw [wire] at hv
        exact (hf x).symm.trans hv
      obtain ⟨r,gt,hr,pin⟩ := least_read n C hL hout i (by omega)
      have p' : Influence n C g (n+r) := .step path hr pin
      by_cases clean : BelowF G C r
      · have hand := (least.1.1 _ (Q0ReaderDeps.S90.gateAt_mem hr)).resolve_right (by
          intro hor
          apply bad
          intro x hx
          apply clean x
          exact Q0ReaderDeps.S90.orStep_up (x:=List.ofFn x) (by simp)
            (.single ⟨r,hr,rfl,hor,pin,least.1.2.1 r hr _ pin⟩) hx)
        exact ⟨r,Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hr,hand,clean⟩,p'⟩
      · exact ih _ (by omega : C.gates.length-r < k) r hr rfl clean p'
  exact go _ g hg rfl dirty .source

theorem common_dominates_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g m : ℕ) (double : DoubleDirty G C m) (gl : g < C.gates.length) (gb : ¬ BelowF G C g)
    (rootOp : (gateAt C g).op = .and ∨ g=m)
    (mixerImplies : ∀ x, W n C x (n+m) = true → W n C x (n+g) = true)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    ∀ t ∈ tops G C, Influence n C g (n+t) → ∀ x, gateVal n C t x=true → gateVal n C g x=true := by
  classical
  have sg : ∀ {w}, Influence n C g w → Kept G C w →
      ∃ i, w = n+i ∧ i < C.gates.length ∧ ((gateAt C i).op = .and ∨ i=m) ∧
        (∀ x, W n C x w = true → W n C x (n+g) = true) := by
    intro w path
    induction path with
    | source => exact fun _ => ⟨g,rfl,gl,rootOp,fun _ h=>h⟩
    | @step j w prev hj pin ih =>
      intro keep
      obtain ⟨i,hw,il,iop,source⟩ := ih (kept_nonclean edge least form hj _ keep pin)
      subst w
      obtain ⟨ops,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C least.1 j hj
      rcases ops with hand|hor
      · refine ⟨j,rfl,hj,Or.inl hand,?_⟩
        intro x hv
        rw [W_and n C x j hj hand _ _ pins ha hb,Bool.and_eq_true] at hv
        rw [pins] at pin
        rcases List.mem_cons.mp pin with eq|tail
        · exact source x (by simpa only [eq] using hv.1)
        · have eq := List.mem_singleton.mp tail
          exact source x (by simpa only [eq] using hv.2)
      · have eq : j = m := by
          rcases iop with andi|rfl
          · by_cases clean : BelowF G C i
            · obtain ⟨reader,out,_⟩ := main_real n G C edge least form
              have rd : j ∈ readers n C i := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,pin⟩
              have ne : n+i ≠ C.output := by
                intro h
                have ix : C.output-n=i := by omega
                rw [ix] at out
                simpa [out] using rd
              obtain ⟨r,only,op,hb⟩ := reader i il clean ne
              rw [only,Finset.mem_singleton] at rd
              subst r
              exact (keep j (Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hj,op,hb⟩) rfl).elim
            · exact dirty_or_eq double least.1 ((S4183.junk_iff G C i).mpr ⟨il,andi,clean⟩) hj pin hor
          · exact (no_mixer_or double least.1 hj pin hor).elim
        subst j
        refine ⟨m,rfl,hj,Or.inr rfl,?_⟩
        exact mixerImplies
  intro t ht path
  apply (sg path ?_).choose_spec.2.2.2
  intro i hi eq
  have same : i=t := by omega
  subst i
  exact GateOp.noConfusion ((Finset.mem_filter.mp ht).2.1.symm.trans (Finset.mem_filter.mp hi).2.1)

private theorem common_dominator_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g m : ℕ) (double : DoubleDirty G C m) (gl : g < C.gates.length) (gb : ¬ BelowF G C g)
    (rootOp : (gateAt C g).op = .and ∨ g=m)
    (mixerImplies : ∀ x, W n C x (n+m) = true → W n C x (n+g) = true)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    (readers n C g).card ≤ 1 := by
  exact dominated_unique G C g gl gb edge least form (live_dirty G C g gl gb edge least)
    (common_dominates_top G C g m double gl gb rootOp mixerImplies edge least form)

theorem mixer_dominates_top {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (double : DoubleDirty G C m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    ∀ t ∈ tops G C, Influence n C m (n+t) → ∀ x, gateVal n C t x=true → gateVal n C m x=true :=
  common_dominates_top G C m m double (mixer_info double).1 (mixer_info double).2.2
    (Or.inr rfl) (fun _ h => h) edge least form

theorem shared_arms_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (g m : ℕ) (double : DoubleDirty G C m) (hg : g ∈ junk G C)
    (both : ∀ w ∈ (gateAt C m).inputs, AndPath n C g w)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    (readers n C g).card ≤ 1 := by
  obtain ⟨gl,ga,gb⟩ := (S4183.junk_iff G C g).mp hg
  apply common_dominator_unique G C g m double gl gb (Or.inl ga) _ edge least form
  intro x active
  obtain ⟨hm,hop,_⟩ := mixer_info double
  obtain ⟨_,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C least.1 m hm
  rw [W_or n C x m hm hop a b pins ha hb,Bool.or_eq_true_iff] at active
  rcases active with v|v
  · exact path_implies_source least.1 (both a (by simp [pins])) x v
  · exact path_implies_source least.1 (both b (by simp [pins])) x v

theorem mixer_unique {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (double : DoubleDirty G C m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    (readers n C m).card ≤ 1 :=
  common_dominator_unique G C m m double (mixer_info double).1 (mixer_info double).2.2
    (Or.inr rfl) (fun _ h => h) edge least form

private theorem first_and_step {n : ℕ} {C : Circuit} {g w : ℕ} (p : AndPath n C g w)
    (ne : w ≠ n+g) : ∃ i < C.gates.length, n+g ∈ (gateAt C i).inputs ∧
      (gateAt C i).op = .and ∧ AndPath n C i w := by
  induction p with
  | source => exact (ne rfl).elim
  | @step v j prev hj hop pin ih =>
    by_cases same : v = n+g
    · exact ⟨j,hj,same ▸ pin,hop,.source⟩
    · obtain ⟨i,hi,reader,op,path⟩ := ih same
      exact ⟨i,hi,reader,op,.step path hj hop pin⟩

theorem no_shared_arm_ancestor {n : ℕ} (G : SimpleGraph (Fin n)) [DecidableRel G.Adj]
    (C : Circuit) (m : ℕ) (double : DoubleDirty G C m)
    (edge : G.edgeFinset.Nonempty) (least : IsLeastAO G C) (form : PEqualNP.TopForm.TopForm G C) :
    ∀ g ∈ junk G C, ¬ (∀ w ∈ (gateAt C m).inputs, AndPath n C g w) := by
  obtain ⟨hm,hor,_⟩ := mixer_info double
  obtain ⟨_,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n C least.1 m hm
  have ma : a ∈ (gateAt C m).inputs := by simp [pins]
  have mb : b ∈ (gateAt C m).inputs := by simp [pins]
  obtain ⟨A,hA,atA⟩ := double.pins 0
  have aid : a = n+A := by simpa [opnd,pins] using atA
  obtain ⟨_,_,badA⟩ := (S4183.junk_iff G C A).mp hA
  have go (k : ℕ) : ∀ g ∈ junk G C, C.size-g=k →
      ¬ (∀ w ∈ (gateAt C m).inputs, AndPath n C g w) := by
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro g hg eq both
      have pa := both a ma
      have pb := both b mb
      have na : a ≠ n+g := by
        intro ex
        have ps : (gateAt C m).inputs = [n+g,b] := by simpa [ex] using pins
        exact no_comparable_or_arms G C least hm hor (Or.inl ps) pb
      have nb : b ≠ n+g := by
        intro ex
        have ps : (gateAt C m).inputs = [a,n+g] := by simpa [ex] using pins
        exact no_comparable_or_arms G C least hm hor (Or.inr ps) pa
      obtain ⟨u,hu,ru,au,pu⟩ := first_and_step pa na
      obtain ⟨v,hv,rv,av,pv⟩ := first_and_step pb nb
      have card := shared_arms_unique G C g m double hg both edge least form
      have single : u = v := by
        by_contra different
        have ur : u ∈ readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hu,ru⟩
        have vr : v ∈ readers n C g := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hv,rv⟩
        have lt := Finset.one_lt_card.mpr ⟨u,ur,v,vr,different⟩
        omega
      subst v
      have bad : ¬ BelowF G C u := by
        intro below
        apply badA
        intro x active
        apply below x
        apply path_implies_source least.1 pu x
        rw [aid]
        exact active
      have junk := (S4183.junk_iff G C u).mpr ⟨hu,au,bad⟩
      have lt := least.1.2.1 u hu _ ru
      have us : u < C.size := hu
      apply ih (C.size-u) (by omega) u junk rfl
      intro w hw
      rw [pins] at hw
      rcases List.mem_cons.mp hw with rfl|rest
      · exact pu
      · obtain rfl := List.mem_singleton.mp rest
        exact pv
  exact fun g hg => go _ g hg rfl

end PEqualNP.Outside.L_meta_4186_aux.Q1Double
