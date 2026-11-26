import Research.IncidenceRestrictedRows
import Mathlib.Data.Fintype.Sum

namespace NatIncidenceRows

open SparseIncidence
open IncidenceRobust (Vertex)

variable {n q : ℕ}

def encode : Vertex n → ℕ
  | .inl p => p.val
  | .inr l => n+l.val

theorem encode_lt (v : Vertex n) : encode v < n+n := by
  cases v with
  | inl p => have := p.isLt; change p.val < n+n; omega
  | inr l => have := l.isLt; change n+l.val < n+n; omega

theorem encode_inj : Function.Injective (@encode n) := by
  intro a b
  cases a with
  | inl p =>
    cases b with
    | inl r => intro e; exact congrArg Sum.inl (Fin.ext e)
    | inr l => intro e; change p.val = n+l.val at e; have := p.isLt; omega
  | inr l =>
    cases b with
    | inl p => intro e; change n+l.val = p.val at e; have := p.isLt; omega
    | inr k => intro e; change n+l.val = n+k.val at e; exact congrArg Sum.inr (Fin.ext (by omega))

theorem decode {a : ℕ} (ha : a < n+n) : ∃ v : Vertex n, encode v = a := by
  by_cases h : a < n
  · exact ⟨.inl ⟨a,h⟩,rfl⟩
  · exact ⟨.inr ⟨a-n,by omega⟩,show n+(a-n) = a by omega⟩

def Edge (I : Fin n → Fin n → Prop) (a b : ℕ) : Prop :=
  ∃ v w : Vertex n, encode v = a ∧ encode w = b ∧ IncidenceRobust.Edge I v w

theorem edge_encode (I : Fin n → Fin n → Prop) (v w : Vertex n) :
    Edge I (encode v) (encode w) ↔ IncidenceRobust.Edge I v w := by
  constructor
  · rintro ⟨a,b,ea,eb,h⟩
    exact encode_inj ea ▸ encode_inj eb ▸ h
  · exact fun h => ⟨v,w,rfl,rfl,h⟩

theorem edge_self (I : Fin n → Fin n → Prop) (a : ℕ) : ¬Edge I a a := by
  rintro ⟨v,w,hv,hw,e⟩
  have eq : v=w := encode_inj (hv.trans hw.symm)
  subst w
  cases v <;> exact e

def mask (n : ℕ) (S : Finset ℕ) : Input n :=
  (fun p => decide (p.val ∈ S),fun l => decide (n+l.val ∈ S))

private theorem mask_pair (v w : Vertex n) :
    mask n {encode v,encode w} = IncidenceRobust.mask {v,w} := by
  apply Prod.ext <;> funext k
  · change decide (encode (Sum.inl k : Vertex n) ∈ _) = _
    simp [IncidenceRobust.mask,encode_inj.eq_iff]
  · change decide (encode (Sum.inr k : Vertex n) ∈ _) = _
    simp [IncidenceRobust.mask,encode_inj.eq_iff]

variable (I : Fin n → Fin n → Prop) [DecidableRel I]

theorem pair_test (out : Set (Input n)) (up : Upward out)
    (pos : ∀ p l, I p l → (single p,single l) ∈ out)
    (neg : ∀ b : Fin n → Bool, Fintype.card {l // b l = true} ≤ q → (outside I b,b) ∉ out)
    (hq : 2 ≤ q) {a c : ℕ} (ha : a < n+n) (hc : c < n+n) :
    mask n {a,c} ∈ out ↔ Edge I a c := by
  obtain ⟨x,rfl⟩ := decode ha
  obtain ⟨y,rfl⟩ := decode hc
  rw [mask_pair,edge_encode]
  exact IncidenceRobust.pair_test I out up pos neg hq x y

variable (degree : ∀ l, Fintype.card {p // I p l} = q+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)

private def deleted (n : ℕ) (D : Finset ℕ) : Finset (Vertex n) :=
  Finset.univ.filter (fun v => encode v ∈ D)

private theorem del_card (D : Finset ℕ) : (deleted n D).card ≤ D.card := by
  apply Finset.card_le_card_of_injOn encode _ encode_inj.injOn
  intro x h
  change x ∈ Finset.univ.filter _ at h
  exact (Finset.mem_filter.mp h).2

include degree unique in
theorem has_neighbor (hq : 0 < q) (hn : n = q^2+q+1) (D : Finset ℕ)
    (small : D.card ≤ q) (a : ℕ) (ha : a < n+n) :
    ∃ c < n+n, c ∉ D ∧ Edge I a c := by
  obtain ⟨v,rfl⟩ := decode ha
  obtain ⟨c,hc,e⟩ := IncidenceRobust.has_neighbor I degree unique hq hn (deleted n D)
    (le_trans (del_card D) small) v
  exact ⟨encode c,encode_lt c,by simpa [deleted] using hc,(edge_encode I v c).2 e⟩

include degree unique in
theorem distinguish (hq : 0 < q) (hn : n = q^2+q+1) (D : Finset ℕ)
    (small : D.card ≤ q) {a b : ℕ} (ha : a < n+n) (hb : b < n+n) (ab : a ≠ b) :
    ∃ c < n+n, c ∉ D ∧ c ≠ a ∧ c ≠ b ∧
    ((Edge I a c ∧ ¬Edge I b c) ∨ (Edge I b c ∧ ¬Edge I a c)) := by
  obtain ⟨v,rfl⟩ := decode ha
  obtain ⟨w,rfl⟩ := decode hb
  have dc := del_card (n:=n) D
  obtain ⟨c,hc,cv,cw,e⟩ := IncidenceRobust.distinguish I degree unique hq hn (deleted n D)
    (by omega) (fun h => ab (congrArg encode h))
  exact ⟨encode c,encode_lt c,by simpa [deleted] using hc,fun h => cv (encode_inj h),
    fun h => cw (encode_inj h),by simpa only [edge_encode] using e⟩

end NatIncidenceRows
