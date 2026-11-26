import ThresholdWarmRetention
import Mathlib.Data.Nat.Sqrt
namespace ThresholdWarmAveraging
open scoped BigOperators
variable {I V : Type*} [DecidableEq I] [DecidableEq V]

theorem missing_total (R : Finset I) (missing : I → Finset I)
    (loss : Finset (Finset I)) (binary : ∀ e∈loss,e.card=2)
    (cover : ∀ r∈R,∀ F∈missing r,F≠r → {r,F}∈loss) :
    (∑ r∈R,(missing r).card)≤2*loss.card+R.card := by
  classical
  let off := fun r => (missing r).erase r
  have enc : (R.sigma off).card≤(loss.sigma (fun e=>e)).card := by
    apply Finset.card_le_card_of_injOn (fun p => ⟨{p.1,p.2},p.1⟩)
    · rintro ⟨r,F⟩ h
      obtain ⟨hr,hF⟩ := Finset.mem_sigma.mp h
      obtain ⟨ne,hm⟩ := Finset.mem_erase.mp hF
      exact Finset.mem_sigma.mpr ⟨cover r hr F hm ne,by simp⟩
    · rintro ⟨r,F⟩ ha ⟨r',F'⟩ hb eq
      have same : r=r' := congrArg (fun p : Σ _ : Finset I, I => p.2) eq
      subst r'
      have keys : ({r,F} : Finset I)={r,F'} := congrArg Sigma.fst eq
      have nf := (Finset.mem_erase.mp (Finset.mem_sigma.mp ha).2).1
      have ff : F=F' := by
        have h : F∈({r,F'}:Finset I) := keys ▸ (by simp)
        simpa [nf] using h
      subst F'
      rfl
  have rhs : (loss.sigma (fun e=>e)).card=2*loss.card := by
    rw [Finset.card_sigma]
    calc
      _ = ∑ _e∈loss, 2 := Finset.sum_congr rfl binary
      _ = _ := by simp [Nat.mul_comm]
  have term (r : I) : (missing r).card≤(off r).card+1 := by
    by_cases h : r∈missing r <;> simp [off,h,Finset.card_erase_of_mem] <;> omega
  have all := Finset.sum_le_sum (fun r (_ : r∈R) => term r)
  rw [Finset.sum_add_distrib] at all
  rw [rhs,Finset.card_sigma] at enc
  simpa using (show (∑ r∈R,(missing r).card)≤2*loss.card+∑ _r∈R,1 by omega)

theorem cold_total (R H : Finset I) (O : Finset V) (cold : I → Finset I)
    (bucket : I → V → Finset I)
    (cover : ∀ r∈R,∀ F∈cold r,F∈H ∧ ∃ S∈O,r∈bucket F S)
    (quota : ∀ F∈H,∀ S∈O,(bucket F S).card≤2) :
    (∑ r∈R,(cold r).card)≤2*H.card*O.card := by
  classical
  let key := fun k : I×V => (bucket k.1 k.2).image (fun r => (r,k.1))
  have inj : (R.sigma cold).card≤((H.product O).biUnion key).card := by
    apply Finset.card_le_card_of_injOn (fun p => (p.1,p.2))
    · rintro ⟨r,F⟩ h
      obtain ⟨hr,hF⟩ := Finset.mem_sigma.mp h
      obtain ⟨hot,S,hs,mem⟩ := cover r hr F hF
      exact Finset.mem_biUnion.mpr ⟨(F,S),Finset.mem_product.mpr ⟨hot,hs⟩,
        Finset.mem_image.mpr ⟨r,mem,rfl⟩⟩
    · rintro ⟨r,F⟩ _ ⟨r',F'⟩ _ eq
      cases eq
      rfl
  have bound (k) (hk : k∈H.product O) : (key k).card≤2 :=
    Finset.card_image_le.trans (quota _ (Finset.mem_product.mp hk).1 _ (Finset.mem_product.mp hk).2)
  rw [←Finset.card_sigma]
  calc
    _ ≤ _ := inj
    _ ≤ _ := Finset.card_biUnion_le
    _ ≤ ∑ _k∈H.product O,2 := Finset.sum_le_sum bound
    _ = _ := by simp [Finset.card_product]; ring

/-- For each high hub B, its >half-degree among all hubs leaves a warm pivot
after discarding low hubs and the retained row's bad pivots. -/
theorem every_high (neighbors low H failed : Finset I) (h u : Nat)
    (cover : neighbors⊆low∪H) (high : h<2*neighbors.card)
    (retained : failed.card≤u) (space : 2*(low.card+u)≤h) :
    ∃ F∈H,F∈neighbors ∧ F∉failed := by
  classical
  by_contra! no
  have sub : neighbors⊆low∪failed := by
    intro F hf
    rcases Finset.mem_union.mp (cover hf) with hl|hh
    · exact Finset.mem_union_left _ hl
    · exact Finset.mem_union_right _ (no F hh hf)
  have count := (Finset.card_le_card sub).trans (Finset.card_union_le _ _)
  omega

theorem prune (R : Finset I) (missing cold : I → Finset I) (u m c : Nat)
    (hm : (∑ r∈R,(missing r).card)≤m) (hc : (∑ r∈R,(cold r).card)≤c) :
    let bad := R.filter (fun r => u<(missing r).card+(cold r).card)
    (u+1)*bad.card≤m+c ∧ ∀ r∈R \ bad, ((missing r)∪(cold r)).card≤u := by
  classical
  intro bad
  constructor
  · have raw := ThresholdColumnPeel.bad_cost R (fun r => (missing r).card+(cold r).card) (u+1)
    rw [Finset.sum_add_distrib] at raw
    exact raw.trans (Nat.add_le_add hm hc)
  · intro r hr
    obtain ⟨inside,no⟩ := Finset.mem_sdiff.mp hr
    have upper : (missing r).card+(cold r).card≤u := by
      by_contra! over
      exact no (Finset.mem_filter.mpr ⟨inside,over⟩)
    exact (Finset.card_union_le _ _).trans upper

/-- One threshold bounds both error parameters: the number of removed rows
and the per-row error count. Use floor(sqrt(total))+1. -/
theorem sqrt_cut (total nBad : Nat)
    (loss : (total.sqrt+2)*nBad≤total) : nBad≤total.sqrt+1 := by
  have sq := Nat.lt_succ_sqrt total
  by_contra! bad
  have p := Nat.mul_le_mul_left (total.sqrt+2) bad.le
  nlinarith
open PEqualNP.CircuitLowerBounds ResidualSurplus T2SoleOrSplice T2CubeDeletion T2RegularOrDelete
open T2OrPartition ThresholdRegularSource ThresholdOrExtraction ThresholdSecondaryReceivers
open ThresholdEffectiveColumns ThresholdWarmSimple ThresholdPivotQuota

theorem native_cold {n out : Nat} {gs : List Raw} (hn : 2≤n)
    (minim : LexMinimum n (source gs out)) (reg : Regular n gs)
    (R H O : Finset (Id (source gs out))) (dis : Disjoint H O)
    (goodR : ∀ r∈R,r∈good (source gs out) n H)
    (pure : ∀ r∈R,(makeBlock (layout n gs out minim.eligible) Fin.val r).exts=[])
    (charged :
      let L := layout n gs out minim.eligible
      ∀ r∈R,∀ F∈exceptional L minim H r,∃ S∈O,
        r∈coldRows L minim F S (ThresholdPivotQuota.eligible L R F S)) :
    let L := layout n gs out minim.eligible
    (∑ r∈R,(exceptional L minim H r).card)≤2*H.card*O.card := by
  classical
  intro L
  apply cold_total R H O _ (fun F S => coldRows L minim F S (ThresholdPivotQuota.eligible L R F S))
  · intro r hr F hf
    exact ⟨(Finset.mem_filter.mp hf).1,charged r hr F hf⟩
  · intro F hf S hs
    have fs : F≠S := by rintro rfl; exact Finset.disjoint_left.mp dis hf hs
    exact (ThresholdPivotQuota.native hn minim reg R H F S fs goodR pure).1

end ThresholdWarmAveraging
