import IncidenceWeightedPlane
import IncidenceWarmPhysical
namespace IncidenceWeightedEdits
open SparseIncidence CircuitRewire IncidenceZeroRestriction IncidenceStartNormalization IncidenceWarmCompiler
theorem edit_cap {n : ℕ} (C : Circuit n) (owners : List ℕ) (drop : Finset ℕ)
    (fork : ℕ→Option ℕ) (start : ℕ→ℕ) (side : ℕ→Bool) (tail : ℕ→List ℕ)
    (pins : ∀ j<C.size,∀ x,fork j=some x→x<n+n)
    (legal : ∀ x∈owners,x<n+n ∧ x∈drop ∧ start x<C.size ∧
      port (C.code (start x)) (side x)=x ∧ (C.code (start x)).op=.meet ∧
      Corridor (n+n) C.size C.code fork x (start x) (tail x))
    (distinct : (owners.flatMap fun x=>start x::tail x).Nodup)
    (bounded : ∀ j∈owners.flatMap (fun x=>start x::tail x),j<C.size)
    (covered : ∀ j<C.size,j∉owners.flatMap (fun x=>start x::tail x)→fork j=none)
    (I : Fin n→Fin n→Prop) [DecidableRel I]
    (degree : ∀ l,Fintype.card {p // I p l}=402)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hn : n=161203)
    (pos : ∀ p l,I p l → (single p,single l)∈editedWire (n+n) C.size C.wire C.code drop fork C.output)
    (neg : ∀ a b : Fin n→Bool, Fintype.card {p // a p=true} ≤ 2 →
      Fintype.card {l // b l=true} ≤ 2 → (∀ p l, a p=true → b l=true → ¬I p l) →
      (a,b) ∉ editedWire (n+n) C.size C.wire C.code drop fork C.output)
    (target : C.size≤646424) : owners.length≤3213 := by
  let l : Fin n := ⟨0,by omega⟩
  have h : 0<Fintype.card {p // I p l} := by rw [degree]; decide
  obtain ⟨⟨p,inc⟩⟩ := Fintype.card_pos_iff.mp h
  obtain ⟨D,budget,bin,out⟩ := compile_owners C owners drop fork start side tail pins legal distinct bounded covered
    ⟨_,pos p l inc⟩
  have yes : flags D I := fun p l inc => out ▸ pos p l inc
  have no : negatives D I 2 2 := fun a b ha hb non => out ▸ neg a b ha hb non
  have lower := IncidenceWeightedPlane.bound I D bin yes no degree unique hn
  omega
#print axioms edit_cap
end IncidenceWeightedEdits
