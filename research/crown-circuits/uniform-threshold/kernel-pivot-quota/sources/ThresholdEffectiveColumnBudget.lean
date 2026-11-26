import ThresholdSharedAndCredit
namespace ThresholdEffectiveColumnBudget
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

/-- Store incomparable missing pairs canonically as unordered two-element finsets. -/
theorem cross_charge (H O : Finset V) (Q : Finset (Finset V))
    (inner : Finset (Finset V)) (choices : V → Finset V)
    (outside : Disjoint O H) (inside : ∀ e∈inner,e⊆H)
    (original : inner⊆Q) (targets : ∀ w∈O,choices w⊆H)
    (missing : ∀ w∈O,∀ v∈choices w,({w,v} : Finset V)∈Q) (d : Nat)
    (many : ∀ w∈O,d≤(choices w).card) :
    d*O.card+inner.card≤Q.card := by
  classical
  let S := O.biUnion (fun w => (choices w).image (fun v => (w,v)))
  let key := fun p : V×V => ({p.1,p.2} : Finset V)
  have spec (p) : p∈S ↔ p.1∈O ∧ p.2∈choices p.1 := by
    cases p with
    | mk a b => simp [S]
  have non (w) (hw : w∈O) : w∉H := Finset.disjoint_left.mp outside hw
  have inj : Set.InjOn key (S : Set (V×V)) := by
    intro p hp r hr same
    obtain ⟨po,pv⟩ := (spec p).mp hp
    obtain ⟨ro,rv⟩ := (spec r).mp hr
    have fst : p.1∈key r := same ▸ (by simp [key] : p.1∈key p)
    have snd : p.2∈key r := same ▸ (by simp [key] : p.2∈key p)
    simp only [key,Finset.mem_insert,Finset.mem_singleton] at fst snd
    obtain a|a := fst
    · obtain b|b := snd
      · exact False.elim ((non _ ro) (b ▸ targets _ po pv))
      · exact Prod.ext a b
    · exact False.elim ((non _ po) (a.symm ▸ targets _ ro rv))
  have into : S.image key ⊆ Q \ inner := by
    intro e he
    obtain ⟨p,hp,rfl⟩ := Finset.mem_image.mp he
    obtain ⟨ho,hv⟩ := (spec p).mp hp
    exact Finset.mem_sdiff.mpr ⟨missing _ ho _ hv,fun hi => non _ ho (inside _ hi (by simp [key]))⟩
  have sub := Finset.card_le_card into
  rw [Finset.card_image_of_injOn inj] at sub
  have tally : S.card=∑ w∈O,(choices w).card := by
    rw [show S=O.biUnion (fun w => (choices w).image (fun v => (w,v))) by rfl, Finset.card_biUnion]
    · apply Finset.sum_congr rfl
      intro w _
      exact Finset.card_image_of_injective _ (fun _ _ eq => congrArg Prod.snd eq)
    · intro a ha b hb ne
      apply Finset.disjoint_left.mpr
      intro p ap bp
      obtain ⟨v,_,e⟩ := Finset.mem_image.mp ap
      obtain ⟨z,_,f⟩ := Finset.mem_image.mp bp
      exact ne (congrArg Prod.fst (e.trans f.symm))
  have pay := Finset.sum_le_sum many
  have partition := Finset.card_sdiff_add_card_eq_card original
  simp only [Finset.sum_const,nsmul_eq_mul,Nat.cast_id] at pay
  rw [Nat.mul_comm] 
  omega

theorem column_budget {h u w o a ash q L K : ℤ}
    (u0 : 0≤u) (room : u≤h) (a0 : 0≤a) (ash0 : a≤ash)
    (count : w≤o+a) (cross : (h-u)*o+L≤q)
    (credit : q+h*ash≤K) : (h-u)*w+L≤K := by
  have pay := mul_le_mul_of_nonneg_left count (sub_nonneg.mpr room)
  have ap := mul_le_mul_of_nonneg_left ash0 (by omega : 0≤h)
  have waste := mul_nonneg u0 a0
  nlinarith only [pay,ap,waste,cross,credit]
#print axioms cross_charge
#print axioms column_budget
end ThresholdEffectiveColumnBudget
