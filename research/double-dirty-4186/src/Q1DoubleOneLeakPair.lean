import Q1DoubleOneLeakCover
import Q1DoubleTrianglePair

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak

open PEqualNP.CircuitLowerBounds PEqualNP.TopForm Private

theorem option_cover_of_batches {n a b w r s : ℕ} {G : SimpleGraph (Fin n)}
    [DecidableRel G.Adj] {C : Circuit} {A : Fin a → Clause n} {B : Fin b → Clause n}
    {W : Fin w → Clause n} (four : NoFourCycle G) (P : Batch G C A W r) (Q : Batch G C B W s)
    (hw : 0<w) (ha : 0<a) (hb : 0<b)
    (ex : ∀ i j k l, s(P.pt i k,P.pt i (!k)) ≠ s(Q.pt j l,Q.pt j (!l)))
    (R H : Finset (Sym2 (Fin n)))
    (reprR : ∀ e ∈ R, ∃ i, e = s(P.pt i false,P.pt i true))
    (reprH : ∀ e ∈ H, ∃ i, e = s(Q.pt i false,Q.pt i true)) :
    ∃ g ∈ pairOptions (a+w) (b+w) w r s, ∃ F, covers F R ∧ covers F H ∧ F.card+g ≤ r+s := by
  classical
  let ok (X : Finset (Fin n)) := (∀ i, ∃ k, P.pt i k ∈ X) ∧ (∀ j, ∃ k, Q.pt j k ∈ X)
  let all (m : ℕ) := ∃ F : Finset (Fin n), ok F ∧ F.card=m
  let X := Finset.univ.image (fun i => P.pt i false)
  let Y := Finset.univ.image (fun j => Q.pt j false)
  have xy : ok (X ∪ Y) := ⟨fun i => ⟨false,Finset.mem_union_left Y
    (Finset.mem_image_of_mem _ (Finset.mem_univ i))⟩,fun j => ⟨false,Finset.mem_union_right X
    (Finset.mem_image_of_mem _ (Finset.mem_univ j))⟩⟩
  have existsSize : ∃ m, all m := ⟨_,X ∪ Y,xy,rfl⟩
  obtain ⟨F,acc,size⟩ := Nat.find_spec existsSize
  have least (D : Finset (Fin n)) (d : ok D) := Nat.find_min' existsSize (show all D.card from ⟨D,d,rfl⟩)
  have rule := Triangle.pair_rule_of_batches four P Q hw ha hb ex (Nat.find existsSize)
    (fun D h₁ h₂ => least D ⟨h₁,h₂⟩)
  have sx : X.card ≤ r := by simpa [X] using (Finset.card_image_le (f := fun i => P.pt i false) (s := Finset.univ))
  have sy : Y.card ≤ s := by simpa [Y] using (Finset.card_image_le (f := fun j => Q.pt j false) (s := Finset.univ))
  have lc := (least _ xy).trans (Finset.card_union_le X Y)
  refine ⟨r+s-Nat.find existsSize, option_of_rule (Nat.sub_le _ _) rule, F, ?_, ?_, by omega⟩
  · intro u v he
    obtain ⟨i,eq⟩ := reprR _ he
    obtain ⟨k,hk⟩ := acc.1 i
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases k <;> tauto
  · intro u v he
    obtain ⟨i,eq⟩ := reprH _ he
    obtain ⟨k,hk⟩ := acc.2 i
    rcases Sym2.eq_iff.mp eq with ⟨rfl,rfl⟩ | ⟨rfl,rfl⟩ <;> cases k <;> tauto

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.OneLeak
