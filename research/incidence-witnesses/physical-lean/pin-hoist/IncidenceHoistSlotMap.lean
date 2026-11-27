import IncidenceHoistEndpoint
namespace IncidenceHoistSlotMap
open CircuitRewire IncidenceStartNormalization IncidenceHoistCompile

def rank (m : Nat) (code : Nat → Gate) (sel : Nat → Option Bool) (j : Nat) :=
  (buildPrefix m code sel j).kept.length

private theorem extendsBy (m : Nat) (code : Nat → Gate) (sel : Nat → Option Bool) (j k : Nat) :
    ∃ tail, (buildPrefix m code sel (j+k)).kept = (buildPrefix m code sel j).kept ++ tail := by
  induction k with
  | zero => exact ⟨[],(List.append_nil _).symm⟩
  | succ k ih =>
    obtain ⟨tail,eq⟩ := ih
    change ∃ tail, (buildPrefix m code sel ((j+k)+1)).kept = (buildPrefix m code sel j).kept ++ tail
    cases h : sel (j+k) with
    | none =>
      refine ⟨tail ++ [redirect (buildPrefix m code sel (j+k)).ref (code (j+k))],?_⟩
      simp only [buildPrefix,h,eq,List.append_assoc]
    | some b =>
      exact ⟨tail,by simpa only [buildPrefix,h] using eq⟩

theorem rank_mono (m : Nat) (code : Nat → Gate) (sel : Nat → Option Bool) :
    Monotone (rank m code sel) := by
  intro j t h
  obtain ⟨k,rfl⟩ := Nat.exists_eq_add_of_le h
  obtain ⟨tail,eq⟩ := extendsBy m code sel j k
  simp only [rank,eq,List.length_append]
  omega

theorem rank_strict (m : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    {j t : Nat} (lt : j<t) (hk : sel j=none) :
    rank m code sel j < rank m code sel t := by
  have step := rank_mono m code sel (show j+1 ≤ t by omega)
  have eq : rank m code sel (j+1) = rank m code sel j + 1 := by simp [rank,buildPrefix,hk]
  omega

def embedding {n : Nat} (C : Circuit n) (sel : Nat → Option Bool) :
    {i : Fin C.size // sel i.val = none} ↪ Fin (circuit C sel).size where
  toFun i := ⟨rank (n+n) C.code sel i.val.val,by
    change _ < C.size
    have h := rank_strict (n+n) C.code sel i.val.isLt i.property
    have eq := prefix_length (n+n) C.code sel C.size
    change rank (n+n) C.code sel C.size + _ = _ at eq
    omega⟩
  inj' := by
    intro a b h
    have e := congrArg Fin.val h
    change rank (n+n) C.code sel a.val.val = rank (n+n) C.code sel b.val.val at e
    apply Subtype.ext
    apply Fin.ext
    rcases lt_trichotomy a.val.val b.val.val with lt|eq|gt
    · have := rank_strict (n+n) C.code sel lt a.property
      omega
    · exact eq
    · have := rank_strict (n+n) C.code sel gt b.property
      omega

theorem physical_gate {n : Nat} (C : Circuit n) (sel : Nat → Option Bool)
    (j : Nat) (hj : j<C.size) (hk : sel j=none) :
    (circuit C sel).code (rank (n+n) C.code sel j) =
      redirect (buildPrefix (n+n) C.code sel j).ref (C.code j) := by
  let m := n+n
  let p := buildPrefix m C.code sel j
  let g := redirect p.ref (C.code j)
  obtain ⟨tail,ext⟩ := extendsBy m C.code sel (j+1) (C.size-(j+1))
  rw [show j+1+(C.size-(j+1))=C.size by omega] at ext
  change (buildPrefix m C.code sel C.size).kept = (buildPrefix m C.code sel (j+1)).kept ++ tail at ext
  simp only [buildPrefix,hk] at ext
  let final := buildPrefix m C.code sel C.size
  change final.kept = (p.kept ++ [g]) ++ tail at ext
  change (codeList m C.size C.output C.code sel).getD p.kept.length _ = g
  change (final.kept ++ appendJoins _ _ _).getD p.kept.length _ = g
  rw [ext]
  simp [List.append_assoc,List.getD_eq_getElem?_getD]

theorem physical_ports {n : Nat} (C : Circuit n) (sel : Nat → Option Bool) (j : Nat)
    (hj : j<C.size) (hk : sel j=none) :
    let g := (circuit C sel).code (rank (n+n) C.code sel j)
    let ref := (buildPrefix (n+n) C.code sel j).ref
    g.op=(C.code j).op ∧ g.left=ref (C.code j).left ∧ g.right=ref (C.code j).right := by
  simp [physical_gate C sel j hj hk,redirect]

theorem kept_ref (m s : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (j : Nat) (hj : j<s) (hk : sel j=none) :
    (buildPrefix m code sel s).ref (m+j) = m + rank m code sel j := by
  have h := IncidenceHoistEndpoint.ref_stable m code sel (j+1) (s-(j+1)) (m+j) (by omega)
  rw [show j+1+(s-(j+1))=s by omega] at h
  rw [h]
  simp [buildPrefix,hk,put,rank]

#print axioms kept_ref
#print axioms embedding
#print axioms physical_ports
end IncidenceHoistSlotMap
