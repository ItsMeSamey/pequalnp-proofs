import ThresholdSlotScan
namespace ThresholdSlotEvaluation
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction ResidualSurplus
open T2OrPartition ThresholdStarRawSlots ThresholdStarBypass ThresholdSimpleIncidence
open T2SoleOrSplice T2RegularOrDelete T2CubeDeletion ThresholdRegularSource

def embed {n k : Nat} {a : Finset (Fin n)} (e : ↥a ≃ Fin k) : Fin k ↪ Fin n :=
  e.symm.toEmbedding.trans (Function.Embedding.subtype _)

theorem arm_vector {C : Circuit} {n k : Nat} (L : Layout C n) (u : Id C)
    (e : ↥(star L u) ≃ Fin k) (s : Finset (Fin k)) :
    rawArm L u e (fun j => decide (j∈s))=fun w => (vector (s.map (embed e))).getD w false := by
  classical
  funext w
  rw [vec_get]
  by_cases h : w<n
  · let x : Fin n := ⟨w,h⟩
    by_cases hx : x∈star L u
    · have mem : x∈s.map (embed e) ↔ e ⟨x,hx⟩∈s := by
        constructor
        · intro hm
          obtain ⟨j,hj,eq⟩ := Finset.mem_map.mp hm
          have sub : e.symm j=⟨x,hx⟩ := Subtype.ext eq
          simpa [←sub] using hj
        · intro hj
          exact Finset.mem_map.mpr ⟨_,hj,by simp [embed]⟩
      simp [rawArm,h,x,show (⟨w,h⟩ : Fin n)∈star L u from hx,show (⟨w,h⟩ : Fin n)∈s.map (embed e) ↔ _ from mem]
    · have no : x∉s.map (embed e) := by
        intro hm
        obtain ⟨j,_,eq⟩ := Finset.mem_map.mp hm
        exact hx (eq ▸ (e.symm j).property)
      simp [rawArm,h,show (⟨w,h⟩ : Fin n)∉star L u from hx,show (⟨w,h⟩ : Fin n)∉s.map (embed e) from no]
  · simp [rawArm,h]

theorem truth {n out k : Nat} {gs : List Raw} (M : LexMinimum n (source gs out))
    (reg : Regular n gs) (u : Id (source gs out)) (x : Fin n)
    (hx : x∈star (layout n gs out M.eligible) u)
    (e : ↥(star (layout n gs out M.eligible) u) ≃ Fin k) (s : Finset (Fin k))
    (V : Nat → Bool)
    (T : Trace (layout n gs out M.eligible)
      (fun i b => input (layout n gs out M.eligible) u x e (fun j => decide (j∈s)) (i,b)) V)
    (stop : next (source gs out) n u=none) : V out=true ↔ 2≤s.card := by
  classical
  let L := layout n gs out M.eligible
  obtain ⟨internal,twice,obs⟩ := regular_inputs n gs out M.eligible reg
  obtain ⟨book,_,_,_,mem⟩ := physical_book L internal Fin.val twice obs
  have rb := split_readback L u x hx e _ V T internal stop book out mem
  rw [arm_vector] at rb
  rw [←rb]
  by_cases hs : s.Nonempty
  · obtain ⟨j,hj⟩ := hs
    have hit : u∈endpoints L ((embed e) j) := (Finset.mem_filter.mp (e.symm j).property).2
    simpa using forced_nonempty_row M reg (fun _ => false) (s.map (embed e)) ((embed e) j) u
      (Finset.mem_map.mpr ⟨_,hj,rfl⟩) hit
  · have nil : s=∅ := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    have hit : u∈endpoints L x := (Finset.mem_filter.mp hx).2
    have one := forced_nonempty_row M reg (fun _ => false) {x} x u (by simp) hit
    have mono := scan_monotone (n+u.val) (fun _ => false) false
      (fun j => (vector (∅ : Finset (Fin n))).getD j false)
      (fun j => (vector {x}).getD j false)
      (by intro j; change (vector (∅ : Finset (Fin n))).getD j false=true → _; rw [vec_get]; split <;> simp)
      (forest L Fin.val) (fun _ => false) (fun _ => false) (fun _ h => h)
    simp only [Finset.map_empty,Finset.card_empty]
    constructor
    · intro on
      have bad := one.mp (mono out on)
      simp at bad
    · omega
end ThresholdSlotEvaluation
