import DDIndexedDAG
import DDIndexedOrigin

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux.Q1Double
open Indexed
attribute [local instance] gateOpDecEq

def nodeIndex (n : ℕ) (C : Circuit) (p : Cuts) : Node → ℕ
  | .row j => rank n C p j
  | .arm b => rank n C p C.size+b.val

private theorem issued {a : Option Gate} (h : a.isSome = true) : ∃ g, a = some g := by
  cases a <;> simp_all

theorem node_injective {n : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard g : ℕ) :
    Set.InjOn (nodeIndex n C p) ((indexed n C p E arms guard).readers g : Set Node) := by
  intro a ha b hb eq
  cases a with
  | row i =>
    obtain ⟨hi,⟨pi,_⟩,_⟩ := (indexed_reads_row C p E arms guard).mp ha
    obtain ⟨gi,ei⟩ := issued pi
    cases b with
    | row j =>
      obtain ⟨hj,⟨pj,_⟩,_⟩ := (indexed_reads_row C p E arms guard).mp hb
      obtain ⟨gj,ej⟩ := issued pj
      change rank n C p i = rank n C p j at eq
      rcases lt_trichotomy i j with h | h | h
      · exact False.elim ((Nat.ne_of_lt (paid_strict C p ei h)) eq)
      · subst j; rfl
      · exact False.elim ((Nat.ne_of_lt (paid_strict C p ej h)) eq.symm)
    | arm t =>
      have lt := paid_strict C p ei hi
      change rank n C p i = rank n C p C.gates.length + t.val at eq
      omega
  | arm s =>
    cases b with
    | row j =>
      obtain ⟨hj,⟨pj,_⟩,_⟩ := (indexed_reads_row C p E arms guard).mp hb
      obtain ⟨gj,ej⟩ := issued pj
      have lt := paid_strict C p ej hj
      change rank n C p C.gates.length + s.val = rank n C p j at eq
      omega
    | arm t =>
      change _ + s.val = _ + t.val at eq
      have h : s=t := Fin.ext (Nat.add_left_cancel eq)
      rw [h]

private theorem sourceAddr {n j i : ℕ} {C : Circuit} {p : Cuts} {b : Fin 2}
    (h : originalSource (pin (build n C p j) n C p j b) = some i) :
    pin (build n C p j) n C p j b = some (.gate i,n+rank n C p i) := by
  cases e : pin (build n C p j) n C p j b with
  | none => simp [e,originalSource] at h
  | some z =>
    rcases z with ⟨o,v⟩
    cases o with
    | input t => simp [e,originalSource] at h
    | gate t =>
      simp [e,originalSource] at h
      subst i
      have hv := pin_address e
      simp_all [address]

theorem row_reader {n i j : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) {D : Circuit} (suffix : List Gate)
    (hd : D.gates = (build n C p C.size).gates ++ suffix)
    (h : Node.row j ∈ (indexed n C p E arms guard).readers i) :
    nodeIndex n C p (.row j) ∈ readers n D (rank n C p i) := by
  obtain ⟨hj,⟨paid,_⟩,b,src⟩ := (indexed_reads_row C p E arms guard).mp h
  obtain ⟨gj,hg⟩ := issued paid
  change j < C.size at hj
  have lt : rank n C p j < (build n C p C.size).gates.length := paid_strict C p hg hj
  have full : D.gates[rank n C p j]? = some gj := by
    rw [hd,List.getElem?_append_left lt]
    exact retains_instruction C p hg hj
  have gate : gateAt D (rank n C p j) = gj := by simp only [gateAt,List.getD_eq_getElem?_getD,full,Option.getD_some]
  have bound : rank n C p j < D.gates.length := by rw [hd,List.length_append]; omega
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_range.mpr bound,?_⟩
  change n+rank n C p i ∈ (gateAt D (rank n C p j)).inputs
  rw [gate]
  have addr := sourceAddr src
  unfold ins at hg
  cases l : pin (build n C p j) n C p j 0 <;> cases r : pin (build n C p j) n C p j 1 <;>
    cases s : p.omit j <;> simp [instruction,l,r,s] at hg
  rw [←hg]
  fin_cases b <;> simp_all

theorem arm_reader {n i : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) (A : Fin 2 → Origin × ℕ) (W : Origin × ℕ)
    (ha : ∀ b, ref (build n C p C.size) (arms b) = some (A b))
    (hw : ref (build n C p C.size) guard = some W)
    {D : Circuit} (suffix : List Gate)
    (hd : D.gates = (build n C p C.size).gates ++
      (⟨.and,[(A 0).2,W.2]⟩ :: ⟨.and,[(A 1).2,W.2]⟩ :: suffix))
    (b : Fin 2) (h : Node.arm b ∈ (indexed n C p E arms guard).readers i) :
    nodeIndex n C p (.arm b) ∈ readers n D (rank n C p i) := by
  obtain ⟨pinID,hp⟩ := (indexed_reads_arm C p E arms guard b).mp h
  change producer (build n C p C.size) _ = some i at hp
  have addr := producer_ref hp
  have mem : n+rank n C p i ∈ [(A b).2,W.2] := by
    by_cases which : pinID = 0
    · simp only [which,if_true] at addr
      rw [ha b] at addr
      have eq := congrArg Prod.snd (Option.some.inj addr)
      exact List.mem_cons.mpr (.inl eq.symm)
    · rw [if_neg which,hw] at addr
      have eq := congrArg Prod.snd (Option.some.inj addr)
      simp [eq]
  apply Finset.mem_filter.mpr
  constructor
  · apply Finset.mem_range.mpr
    change rank n C p C.size + b.val < D.gates.length
    rw [hd,List.length_append]
    have := b.isLt
    simp only [rank,List.length_cons]; omega
  · change _ ∈ (gateAt D (rank n C p C.size + b.val)).inputs
    have gate : gateAt D (rank n C p C.size + b.val) = ⟨.and,[(A b).2,W.2]⟩ := by
      simp only [gateAt,List.getD_eq_getElem?_getD,hd, List.getElem?_append_right (Nat.le_add_right _ _)]
      fin_cases b <;> simp [rank]
    rwa [gate]

theorem readers_card {n i : ℕ} (C : Circuit) (p : Cuts) (E : Finset ℕ)
    (arms : Fin 2 → ℕ) (guard : ℕ) (A : Fin 2 → Origin × ℕ) (W : Origin × ℕ)
    (ha : ∀ b, ref (build n C p C.size) (arms b) = some (A b))
    (hw : ref (build n C p C.size) guard = some W)
    {D : Circuit} (suffix : List Gate)
    (hd : D.gates = (build n C p C.size).gates ++
      (⟨.and,[(A 0).2,W.2]⟩ :: ⟨.and,[(A 1).2,W.2]⟩ :: suffix)) :
    ((indexed n C p E arms guard).readers i).card ≤ (readers n D (rank n C p i)).card := by
  apply Finset.card_le_card_of_injOn (nodeIndex n C p)
  · intro v hv
    cases v with
    | row j => exact row_reader C p E arms guard _ hd hv
    | arm b => exact arm_reader C p E arms guard A W ha hw _ hd b hv
  · exact node_injective C p E arms guard i

end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
