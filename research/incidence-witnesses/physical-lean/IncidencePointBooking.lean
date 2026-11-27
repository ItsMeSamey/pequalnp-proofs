import IncidencePointHeavy
import IncidenceStartNormalization
namespace IncidencePointBooking
open IncidencePointHeavy CircuitRewire SparseQueryCut
open scoped BigOperators
variable {P V : Type*} [DecidableEq P] [Fintype V] [DecidableEq V]

private theorem forces (H : P→Finset V) (over : ∀ a b,a≠b → (H a ∩ H b).card≤1)
    (x : P) (W : Finset P) (few : W.card≤2) (K : Finset V) (big : 3≤(K∩H x).card)
    (inside : K⊆W.biUnion H) : x∈W := by
  classical
  by_contra out
  let F := fun y=>H x ∩ H y
  have sub : K∩H x⊆W.biUnion F := by
    intro l hl
    obtain ⟨k,h⟩ := Finset.mem_inter.mp hl
    obtain ⟨y,yw,ly⟩ := Finset.mem_biUnion.mp (inside k)
    exact Finset.mem_biUnion.mpr ⟨y,yw,Finset.mem_inter.mpr ⟨h,ly⟩⟩
  have bound : (K∩H x).card≤W.card := calc
    _ ≤ (W.biUnion F).card := Finset.card_le_card sub
    _ ≤ ∑ y∈W,(F y).card := Finset.card_biUnion_le
    _ ≤ ∑ _y∈W,1 := Finset.sum_le_sum fun y hy=>over x y (fun e=>out (e ▸ hy))
    _ = _ := by simp
  omega

theorem booking (m s : Nat) (X : Nat→Set (Finset V)) (C : Finset P) (H : P→Finset V)
    (W : P→Finset P) (over : ∀ a b,a≠b → (H a ∩ H b).card≤1)
    (few : ∀ x∈C,(W x).card≤2)
    (anti : ∀ x∈C,∀ y∈C,x≠y → x∈W y → y∉W x) (r : Nat)
    (low : ∀ x∈C,r≤(heavySlots m s X ((W x).biUnion H) (H x)).card) : C.card*r≤s := by
  classical
  let G := fun x=>heavySlots m s X ((W x).biUnion H) (H x)
  have dis : (C : Set P).PairwiseDisjoint G := by
    intro x hx y hy ne
    apply Finset.disjoint_left.mpr
    intro j jx jy
    obtain ⟨bigx,insx⟩ := (Finset.mem_filter.mp jx).2
    obtain ⟨bigy,insy⟩ := (Finset.mem_filter.mp jy).2
    exact anti x hx y hy ne (forces H over x _ (few _ hy) _ bigx insy)
      (forces H over y _ (few _ hx) _ bigy insx)
  have sub : C.biUnion G⊆Finset.range s := by
    intro j hj
    obtain ⟨x,_,h⟩ := Finset.mem_biUnion.mp hj
    exact (Finset.mem_filter.mp h).1
  calc
    _ = ∑ _x∈C,r := by simp
    _ ≤ ∑ x∈C,(G x).card := Finset.sum_le_sum low
    _ = (C.biUnion G).card := (Finset.card_biUnion dis).symm
    _ ≤ _ := by simpa using Finset.card_le_card sub

theorem census (m s : Nat) (raw : Nat→Gate) (X : Nat→Set (Finset V))
    (C : Finset P) (H : P→Finset V) (W : P→Finset P) (o : P→Nat)
    (over : ∀ a b,a≠b → (H a ∩ H b).card≤1)
    (few : ∀ x∈C,(W x).card≤2) (anti : ∀ x∈C,∀ y∈C,x≠y → x∈W y → y∉W x)
    (top : ∀ j<s,(raw j).left<m+j ∧ (raw j).right<m+j)
    (sem : ∀ j<s,X (m+j)=(raw j).eval X)
    (input : ∀ j<m,(profile X j).card≤1)
    (up : ∀ j<m+s,∀ l : V,∀ T : Finset V,l∈T → {l}∈X j → T∈X j)
    (bound : ∀ x∈C,o x<m+s) (star : ∀ x∈C,(H x).card=402)
    (pos : ∀ x∈C,∀ l∈H x,({l} : Finset V)∈X (o x))
    (neg : ∀ x∈C,∀ T : Finset V,T.card≤199 → Disjoint T ((W x).biUnion H) → T∉X (o x))
    (size : s≤646424) (edited total : Nat) (partition : total=edited+C.card) (paid : edited≤3213) :
    total≤6461 := by
  apply IncidenceStartNormalization.point_census partition _ paid
  apply Nat.le_trans _ size
  rw [Nat.mul_comm]
  apply booking m s X C H W over few anti 199
  intro x hx
  apply physical_charge m s (o x) raw X (bound x hx) top sem _ _ 199
    (by rw [star x hx]; decide) _ up (pos x hx) (neg x hx)
  intro j hj
  exact Or.inl ((Finset.card_le_card Finset.inter_subset_left).trans ((input j hj).trans (by decide)))
#print axioms booking
#print axioms census
end IncidencePointBooking
