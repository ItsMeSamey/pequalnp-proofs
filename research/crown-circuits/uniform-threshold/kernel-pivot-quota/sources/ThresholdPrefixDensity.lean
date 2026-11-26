import ThresholdProbeIdeals
import Mathlib.Data.Finset.Sort
namespace ThresholdPrefixDensity
open ThresholdProbeIdeals
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V]
theorem prefix_lengths (Q : Finset (V×V)) (rank : V→Nat) (h : Nat)
    (forward : ∀ p∈Q,rank p.1<rank p.2 ∧ rank p.2<h)
    (B : Nat) (bound : ∀ I,Ideal Q I → (Cut Q I).card≤B) :
    (∑ p∈Q,(rank p.2-rank p.1))≤h*B := by
  classical
  let I := fun j : Nat => Finset.univ.filter (fun v => rank v≤j)
  have ideal (j) : Ideal Q (I j) := by
    intro a b ab inside
    have lt : rank a < rank b := (forward (a,b) ab).1
    have le := (Finset.mem_filter.mp inside).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by omega⟩
  have length (p : V×V) (hp : p∈Q) :
      (∑ j∈Finset.range h,(if rank p.1≤j ∧ j<rank p.2 then 1 else 0 : Nat))=rank p.2-rank p.1 := by
    have top := (forward p hp).2
    have interval : (Finset.range h).filter (fun j => rank p.1≤j ∧ j<rank p.2)=Finset.Ico (rank p.1) (rank p.2) := by
      ext j
      simp only [Finset.mem_filter,Finset.mem_range,Finset.mem_Ico]
      omega
    simp only [Finset.sum_boole,interval,Nat.card_Ico,Nat.cast_id]
  have column (j : Nat) :
      (∑ p∈Q,(if rank p.1≤j ∧ j<rank p.2 then 1 else 0 : Nat))=(Cut Q (I j)).card := by
    simp only [Finset.sum_boole,Cut,Nat.cast_id]
    congr 1
    ext p
    simp [I]
  calc
    _ = ∑ p∈Q,∑ j∈Finset.range h,(if rank p.1≤j ∧ j<rank p.2 then 1 else 0 : Nat) :=
      Finset.sum_congr rfl (fun p hp => (length p hp).symm)
    _ = ∑ j∈Finset.range h,(Cut Q (I j)).card := by rw [Finset.sum_comm]; simp_rw [column]
    _ ≤ ∑ _∈Finset.range h,B := Finset.sum_le_sum (fun j _ => bound _ (ideal j))
    _ = _ := by simp
theorem split_at (Q : Finset (V×V)) (rank : V→Nat) (h B L : Nat)
    (rank1 : Set.InjOn rank ((Q.image Prod.fst : Finset V) : Set V))
    (rank2 : Set.InjOn rank ((Q.image Prod.snd : Finset V) : Set V))
    (forward : ∀ p∈Q,rank p.1<rank p.2 ∧ rank p.2<h)
    (bound : ∀ I,Ideal Q I → (Cut Q I).card≤B) :
    Q.card*L ≤ h*L^2+h*B := by
  classical
  let S := Q.filter (fun p => rank p.2-rank p.1≤L)
  let T := Q.filter (fun p => ¬rank p.2-rank p.1≤L)
  let code := fun p : V×V => (rank p.1,rank p.2-rank p.1-1)
  have short : S.card≤h*L := by
    have mem (p) (hp : p∈S) : code p∈Finset.range h ×ˢ Finset.range L := by
      obtain ⟨hq,low⟩ := Finset.mem_filter.mp hp
      obtain ⟨rise,top⟩ := forward p hq
      exact Finset.mem_product.mpr ⟨Finset.mem_range.mpr (by dsimp [code]; omega),
        Finset.mem_range.mpr (by dsimp [code]; omega)⟩
    have inj : (S : Set (V×V)).InjOn code := by
      intro a ha b hb eq
      have aq : a∈Q := (Finset.mem_filter.mp ha).1
      have bq : b∈Q := (Finset.mem_filter.mp hb).1
      have one := congrArg Prod.fst eq
      have two := congrArg Prod.snd eq
      change rank a.1=rank b.1 at one
      change rank a.2-rank a.1-1=rank b.2-rank b.1-1 at two
      have al := (forward a aq).1
      have bl := (forward b bq).1
      exact Prod.ext (rank1 (Finset.mem_image_of_mem _ aq) (Finset.mem_image_of_mem _ bq) one)
        (rank2 (Finset.mem_image_of_mem _ aq) (Finset.mem_image_of_mem _ bq) (by omega))
    simpa using Finset.card_le_card_of_injOn code mem inj
  have long : T.card*L≤h*B := by
    have lo := Finset.sum_le_sum (s:=T) (fun p hp => show L≤rank p.2-rank p.1 by
      have hi := (Finset.mem_filter.mp hp).2; omega)
    have cap : (∑ p∈T,(rank p.2-rank p.1))≤∑ p∈Q,(rank p.2-rank p.1) :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ Q)
        (fun p _ _ => Nat.zero_le (rank p.2-rank p.1))
    have head : T.card*L ≤ ∑ p∈T, (rank p.2-rank p.1) := by simpa using lo
    exact (head.trans cap).trans (prefix_lengths Q rank h forward B bound)
  have part : S.card+T.card=Q.card := Finset.card_filter_add_card_filter_not _
  rw [←part,Nat.add_mul]
  have pay := Nat.mul_le_mul_right L short
  simpa only [pow_two,Nat.mul_assoc] using Nat.add_le_add pay long
#print axioms split_at
end ThresholdPrefixDensity
