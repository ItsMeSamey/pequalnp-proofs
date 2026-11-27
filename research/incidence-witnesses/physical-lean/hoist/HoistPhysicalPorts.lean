import IncidenceHoistWalk
import IncidenceHoistCompile
import IncidenceHoistPorts
namespace HoistPhysicalPorts
open CircuitRewire IncidenceStartNormalization IncidenceHoistCompile IncidenceHoistFlow
open IncidenceHoistWalk IncidenceHoistPorts

private def siblings (w : Op → Nat) (i : Nat) (xs : List Nat) :=
  (xs.map fun x => w .join * hit x i).sum

private theorem append_count (w : Op → Nat) (i : Nat) (xs ys : List Gate) :
    count w i (xs++ys) = count w i xs + count w i ys := by simp [count]

private theorem sum_ports (g : Gate) (w : Op → Nat) (i : Nat) :
    count w i [g] = w g.op * (hit g.left i + hit g.right i) := by simp [count]
private theorem prefix_counts (m : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (i : Nat) (w : Op → Nat) (hi : i<m) (t : Nat)
    (main : ∀ j<t, ∀ b, sel j=some b → (code j).op=.join ∧ IncidenceHoistFlow.keep (code j) b ≠ i) :
    let p := buildPrefix m code sel t
    (∀ v, p.ref v=i ↔ v=i) ∧ count w i p.kept + siblings w i p.siblings =
      count w i ((List.range t).map code) := by
  induction t with
  | zero => simp [buildPrefix,count,siblings]
  | succ t ih =>
    let p := buildPrefix m code sel t
    obtain ⟨ref,ind⟩ := ih (fun j hj => main j (by omega))
    change count w i p.kept + siblings w i p.siblings = _ at ind
    have hits (v : Nat) : hit (p.ref v) i = hit v i := by simp only [hit,p,ref]
    have past : m+t ≠ i := by omega
    rw [List.range_succ,List.map_append,append_count]
    simp only [List.map_cons,List.map_nil,sum_ports]
    cases e : sel t with
    | none =>
      simp only [buildPrefix,e]
      constructor
      · intro v
        by_cases eq : v=m+t
        · subst v
          simp [put,past]
          omega
        · simpa only [put,if_neg eq] using ref v
      · rw [append_count,sum_ports]
        change count w i p.kept + w (code t).op * (hit (p.ref (code t).left) i +
          hit (p.ref (code t).right) i) + siblings w i p.siblings = _
        rw [hits,hits]
        omega
    | some b =>
      obtain ⟨op,skip⟩ := main t (by omega) b e
      simp only [buildPrefix,e]
      constructor
      · intro v
        by_cases eq : v=m+t
        · subst v
          simp [put,ref,skip,past]
        · simpa only [put,if_neg eq] using ref v
      · have side : hit (code t).left i + hit (code t).right i =
              hit (other (code t) b) i := by
          cases b <;> simp [IncidenceHoistFlow.keep] at skip <;> simp [other,hit,skip]
        have extra : siblings w i (p.siblings ++ [p.ref (other (code t) b)]) =
            siblings w i p.siblings + w .join * hit (other (code t) b) i := by simp [siblings,hits]
        change count w i p.kept + siblings w i (p.siblings ++ [p.ref (other (code t) b)]) = _
        rw [extra,side,op]
        omega

private theorem aggregator (w : Op → Nat) (i n a : Nat) (hn : i<n) (ha : a≠i) (xs : List Nat) :
    count w i (appendJoins n a xs) = siblings w i xs := by
  induction xs generalizing n a with
  | nil => rfl
  | cons x xs ih =>
    have rest := ih (n+1) n (by omega) (by omega)
    change w .join * (hit a i + hit x i) + count w i (appendJoins (n+1) n xs) = _
    rw [rest]
    simp [siblings,hit,ha]

theorem physical_count (m s out i : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (w : Op → Nat) (hi : i<m) (ho : out≠i)
    (main : ∀ j<s, ∀ b, sel j=some b → (code j).op=.join ∧ IncidenceHoistFlow.keep (code j) b ≠ i) :
    count w i (codeList m s out code sel) = count w i ((List.range s).map code) := by
  obtain ⟨ref,h⟩ := prefix_counts m code sel i w hi s main
  unfold codeList
  rw [append_count,aggregator]
  · exact h
  · omega
  · exact fun eq => ho ((ref out).mp eq)

private theorem walk_main {n} (C : Circuit n) (x i fuel : Nat) (hi : i<n+n) (hx : x≠i) :
    ∀ e ∈ walk C fuel x, IncidenceHoistFlow.keep (C.code e.1) e.2 ≠ i := by
  induction fuel generalizing x with
  | zero => simp [walk]
  | succ f ih =>
    cases step : step? C x with
    | none => simp [walk,step]
    | some e =>
      obtain ⟨j,b⟩ := e
      simp only [walk,step,List.mem_cons]
      rintro e (rfl|mem)
      · exact fun eq => hx ((step_sound C step).1.reads.symm.trans eq)
      · exact ih _ (by omega) _ mem

theorem selected_main {n} (C : Circuit n) (line : Bool) (i : Nat) (hi : i<n+n)
    (otherShore : ∀ x : Fin n, IncidenceHoistShield.owner line x ≠ i)
    (j : Nat) (b : Bool) (s : select C line j = some b) :
    IncidenceHoistFlow.keep (C.code j) b ≠ i := by
  obtain ⟨x,hx⟩ := selected_mem C s
  exact walk_main C _ _ _ hi (otherShore x) (j,b) hx

theorem circuit_code {n} (C : Circuit n) (sel : Nat → Option Bool) :
    circuitCode (circuit C sel) = codeList (n+n) C.size C.output C.code sel := by
  let gs := codeList (n+n) C.size C.output C.code sel
  change (List.range C.size).map (fun j => gs.getD j ⟨.zero,0,0⟩) = gs
  have len : gs.length = C.size := physical_size ..
  apply List.ext_getElem
  · simp [len]
  · intro i hi hj
    have bound : i < gs.length := hj
    simp [List.getD_eq_getElem?_getD,bound]

theorem opposite_count {n} (C : Circuit n) (I : Fin n→Fin n→Prop)
    (neg : negatives C I n 401) (line : Bool) (x : Fin n) (w : Op → Nat) :
    let i := IncidenceHoistShield.owner (!line) x
    count w i (circuitCode (circuit C (select C line))) = count w i (circuitCode C) := by
  let i := IncidenceHoistShield.owner (!line) x
  have hot := owner_hot C (!line) x
  have cold := witness_neg C I neg (!line) x
  have out : C.output ≠ i := fun e => cold (e ▸ hot)
  have hi : i < n+n := by cases line <;> simp [i,IncidenceHoistShield.owner] <;> omega
  have foreign (u : Fin n) : IncidenceHoistShield.owner line u ≠ i := by
    cases line <;> simp [i,IncidenceHoistShield.owner] <;> omega
  rw [circuit_code]
  exact physical_count _ _ _ _ _ _ w hi out (fun j _ b s =>
    ⟨(selected_safe C neg s).choose_spec.1,selected_main C line i hi foreign j b s⟩)

theorem opposite_uses {n} (C : Circuit n) (I : Fin n→Fin n→Prop)
    (neg : negatives C I n 401) (line : Bool) (x : Fin n) :
    IncidenceStartNormalization.uses (circuit C (select C line)) (IncidenceHoistShield.owner (!line) x) =
    IncidenceStartNormalization.uses C (IncidenceHoistShield.owner (!line) x) := by
  simpa only [← actual_uses] using opposite_count C I neg line x (fun _ => 1)

private theorem oldHit {x i a j : Nat} (imp : x=i → a=j) : hit x i ≤ hit a j := by
  by_cases h : x=i
  · simp [hit,h,imp h]
  · simp [hit,h]

private theorem aggregator_le (w : Op → Nat) (i n a : Nat) (xs : List Nat) :
    siblings w i xs ≤ count w i (appendJoins n a xs) := by
  induction xs generalizing n a with
  | nil => exact le_rfl
  | cons x xs ih =>
    change w .join * hit x i + siblings w i xs ≤
      w .join * (hit a i + hit x i) + count w i (appendJoins (n+1) n xs)
    rw [Nat.mul_add]
    have := ih (n+1) n
    omega

theorem exit_count_le (m s out src dst : Nat) (code : Nat → Gate) (sel : Nat → Option Bool)
    (w : Op → Nat)
    (reads : ∀ t<s, (code t).left=src ∨ (code t).right=src →
      (buildPrefix m code sel t).ref src=dst)
    (skip : ∀ t<s, ∀ b, sel t=some b → (code t).op=.join ∧ IncidenceHoistFlow.keep (code t) b≠src) :
    count w src ((List.range s).map code) ≤ count w dst (codeList m s out code sel) := by
  have inductionBound (t : Nat) (ht : t≤s) :
      let p := buildPrefix m code sel t
      count w src ((List.range t).map code) ≤ count w dst p.kept + siblings w dst p.siblings := by
    induction t with
    | zero => simp [buildPrefix,count,siblings]
    | succ t ih =>
      let p := buildPrefix m code sel t
      have prev := ih (by omega)
      have left : hit (code t).left src ≤ hit (p.ref (code t).left) dst := by
        apply oldHit
        intro e
        rw [e]
        exact reads t (by omega) (Or.inl e)
      have right : hit (code t).right src ≤ hit (p.ref (code t).right) dst := by
        apply oldHit
        intro e
        rw [e]
        exact reads t (by omega) (Or.inr e)
      rw [List.range_succ,List.map_append,append_count]
      simp only [List.map_cons,List.map_nil,sum_ports]
      change _ ≤ count w dst p.kept + siblings w dst p.siblings at prev
      cases e : sel t with
      | none =>
        simp only [buildPrefix,e,append_count,sum_ports]
        have le := Nat.mul_le_mul_left (w (code t).op) (Nat.add_le_add left right)
        change _ ≤ count w dst p.kept + w (code t).op *
          (hit (p.ref (code t).left) dst + hit (p.ref (code t).right) dst) + siblings w dst p.siblings
        omega
      | some b =>
        obtain ⟨op,non⟩ := skip t (by omega) b e
        have side : hit (code t).left src + hit (code t).right src ≤
            hit (p.ref (other (code t) b)) dst := by
          cases b <;> simp [IncidenceHoistFlow.keep] at non <;>
            simp [other,hit,non] at left right ⊢ <;> omega
        have le := Nat.mul_le_mul_left (w .join) side
        simp only [buildPrefix,e,op]
        change _ ≤ count w dst p.kept + siblings w dst (p.siblings ++ [p.ref (other (code t) b)])
        have add : siblings w dst (p.siblings ++ [p.ref (other (code t) b)]) =
            siblings w dst p.siblings + w .join * hit (p.ref (other (code t) b)) dst := by simp [siblings]
        rw [add]
        omega
  unfold codeList
  rw [append_count]
  exact le_trans (inductionBound s le_rfl) (Nat.add_le_add_left (aggregator_le ..) _)

theorem count_pos_iff (gs : List Gate) (w : Op → Nat) (i : Nat) :
    0 < count w i gs ↔ ∃ g ∈ gs, 0 < w g.op ∧ (g.left=i ∨ g.right=i) := by
  induction gs with
  | nil => simp [count]
  | cons g gs ih =>
    change 0 < w g.op * (hit g.left i + hit g.right i) + count w i gs ↔ _
    simp only [Nat.add_pos_iff_pos_or_pos,ih,List.mem_cons]
    by_cases hl : g.left=i <;> by_cases hr : g.right=i <;>
      simp [hit,hl,hr] <;> grind

theorem circuit_count_pos {n} (C : Circuit n) (w : Op → Nat) (i : Nat) :
    0 < count w i (circuitCode C) ↔
      ∃ g<C.size, 0 < w (C.code g).op ∧ ((C.code g).left=i ∨ (C.code g).right=i) := by
  rw [count_pos_iff]
  constructor
  · rintro ⟨g,hg,hw,h⟩
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    exact ⟨_,List.mem_range.mp hj,hw,h⟩
  · rintro ⟨j,hj,hw,h⟩
    exact ⟨_,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩,hw,h⟩

theorem opposite_and_line {n} (C : Circuit n) (I : Fin n→Fin n→Prop)
    (neg : negatives C I n 401) (old : soleAnd C n) :
    soleAnd (circuit C (select C false)) n := by
  intro j hj hu g hg port
  let x : Fin n := ⟨j,hj⟩
  have he := opposite_uses C I neg false x
  change IncidenceStartNormalization.uses _ (n+j) = IncidenceStartNormalization.uses C (n+j) at he
  have oldone := he ▸ hu
  by_contra bad
  let w := fun op : Op => if op = .meet then 0 else 1
  have pos := (circuit_count_pos (circuit C (select C false)) w (n+j)).mpr
    ⟨g,hg,by simp [w,bad],port⟩
  have hc := opposite_count C I neg false x w
  change count w (n+j) _ = count w (n+j) (circuitCode C) at hc
  rw [hc] at pos
  obtain ⟨k,hk,pos,reads⟩ := (circuit_count_pos C w _).mp pos
  simp [w,old j hj oldone k hk reads] at pos

#print axioms opposite_and_line
#print axioms opposite_count
#print axioms opposite_uses
#print axioms exit_count_le
end HoistPhysicalPorts
