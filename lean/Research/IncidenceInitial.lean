import Research.IncidenceBound
import Research.SparseIncidence
import Research.CircuitRewire
import Research.NatIncidenceRows

namespace IncidenceInitial

open SparseIncidence CircuitRewire

theorem build {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hn : n = q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (s o : ℕ) (X : ℕ → Set (Input n)) (ho : o < n+n+s)
    (inputs : ∀ p : Fin n, X p.val = {z | z.1 p = true} ∧ X (n+p.val) = {z | z.2 p = true})
    (steps : ∀ k < s, ∃ a < n+n+k, ∃ b < n+n+k,
      X (n+n+k) = X a ∪ X b ∨ X (n+n+k) = X a ∨ X (n+n+k) = ∅ ∨ X (n+n+k) = X a ∩ X b)
    (pos : ∀ p l, I p l → (single p,single l) ∈ X o)
    (row : Finset ℕ → Input n)
    (left : ∀ T p, (row T).1 p = true ↔ p.val ∈ T)
    (right : ∀ T l, (row T).2 l = true ↔ n+l.val ∈ T)
    (E : ℕ → ℕ → Prop)
    (pairs : Upward (X o) → ∀ a<n+n, ∀ b<n+n, row {a,b} ∈ X o ↔ E a b) :
    ∃ (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set (Finset ℕ)),
      t ≤ s ∧ out < n+n+t ∧
      (∀ k<t, Normal (code k) (n+n+k) ∧ Y (n+n+k) = (code k).eval Y) ∧
      (∀ j<n+n, Y j = {T | j∈T}) ∧
      ∀ a<n+n, ∀ b<n+n, {a,b} ∈ Y out ↔ E a b := by
  obtain ⟨S,sub,_,sup⟩ := IncidenceBound.support (n+n) s X steps o ho
  have up : Upward (X o) := by
    intro u v le
    apply sup u v
    intro j hj
    have jb := Finset.mem_range.mp (sub hj)
    by_cases lo : j < n
    · let p : Fin n := ⟨j,lo⟩
      rw [(inputs p).1]
      exact le.1 p
    · let l : Fin n := ⟨j-n,by omega⟩
      have eq : j = n+l.val := by dsimp [l]; omega
      rw [eq,(inputs l).2]
      exact le.2 l
  let W := fun j => row ⁻¹' X j
  have live : (W o).Nonempty := by
    let l : Fin n := ⟨0,by omega⟩
    have incident : Nonempty {p // I p l} := Fintype.card_pos_iff.mp (by rw [degree]; omega)
    obtain ⟨⟨p,inc⟩⟩ := incident
    refine ⟨{p.val,n+l.val},up ?_ (pos p l inc)⟩
    constructor
    · intro i hi
      apply (left _ i).2
      have eq : i=p := of_decide_eq_true hi
      simp [eq]
    · intro j hj
      apply (right _ j).2
      have eq : j=l := of_decide_eq_true hj
      simp [eq]
  obtain ⟨raw,ord,sem⟩ := select_gates _ _ X steps
  have laws (g : ℕ) (hg : g<s) : W (n+n+g) = (raw g).eval W := by
    dsimp [W]; rw [sem g hg,preimage_gate]
  obtain ⟨t,out,code,Y,le,_,hout,eq,ip,gate⟩ := restrict_mask (n+n) s o raw W ∅ ho
      (by simp) live ord laws
  refine ⟨t,out,code,Y,le,hout,fun k hk => ⟨(gate k hk).1,(gate k hk).2.1⟩,?_,?_⟩
  · intro j hj
    rw [ip j hj]
    ext T
    by_cases lo : j < n
    · let p : Fin n := ⟨j,lo⟩
      change row T ∈ X p.val ↔ j ∈ T
      rw [(inputs p).1]
      exact left T p
    · let l : Fin n := ⟨j-n,by omega⟩
      have e : j=n+l.val := by dsimp [l]; omega
      change row T ∈ X j ↔ j ∈ T
      rw [e,(inputs l).2]
      exact right T l
  · intro a ha b hb
    rw [← eq]
    exact pairs up a ha b hb

theorem initial {n q : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (hq : 2 ≤ q) (hn : n = q^2+q+1) (degree : ∀ l, Fintype.card {p // I p l} = q+1)
    (s o : ℕ) (X : ℕ → Set (Input n)) (ho : o < n+n+s)
    (inputs : ∀ p : Fin n, X p.val = {z | z.1 p = true} ∧ X (n+p.val) = {z | z.2 p = true})
    (steps : ∀ k < s, ∃ a < n+n+k, ∃ b < n+n+k,
      X (n+n+k) = X a ∪ X b ∨ X (n+n+k) = X a ∨ X (n+n+k) = ∅ ∨ X (n+n+k) = X a ∩ X b)
    (pos : ∀ p l, I p l → (single p,single l) ∈ X o)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l = true} ≤ q → (outside I b,b) ∉ X o) :
    ∃ (t out : ℕ) (code : ℕ → Gate) (Y : ℕ → Set (Finset ℕ)),
      t ≤ s ∧ out < n+n+t ∧
      (∀ k<t, Normal (code k) (n+n+k) ∧ Y (n+n+k) = (code k).eval Y) ∧
      (∀ j<n+n, Y j = {T | j∈T}) ∧
      ∀ a<n+n, ∀ b<n+n, {a,b} ∈ Y out ↔ NatIncidenceRows.Edge I a b := by
  apply build I hn degree s o X ho inputs steps pos (NatIncidenceRows.mask n)
    (fun T p => by simp [NatIncidenceRows.mask]) (fun T l => by simp [NatIncidenceRows.mask])
  exact fun up _ ha _ hb => NatIncidenceRows.pair_test I _ up pos neg hq ha hb

end IncidenceInitial
