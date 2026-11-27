import IncidenceHoistSensitive
namespace IncidencePinHoistSparse
open CircuitRewire SparseIncidence IncidenceStartNormalization IncidenceHoistSparse
open IncidenceHoistPrefix IncidenceHoistWalk IncidenceHoistShield IncidenceHoistFlow
open IncidenceHoistReaders
variable {n : Nat}
def mask (s : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ s)
def active (a : Fin n → Bool) := Finset.univ.filter (fun i => a i = true)
theorem mask_active (a : Fin n → Bool) : mask (active a) = a := by
  funext i
  simp [mask,active]
theorem count_mask (s : Finset (Fin n)) :
    Fintype.card {i // mask s i = true} = s.card := by
  simp [Fintype.card_subtype,mask]
theorem count_active (a : Fin n → Bool) :
    (active a).card = Fintype.card {i // a i = true} := by
  rw [← count_mask,mask_active]

def view (line : Bool) (s t : Finset (Fin n)) : Input n :=
  if line then (mask t,mask s) else (mask s,mask t)

theorem view_mono (line : Bool) {a b c d : Finset (Fin n)}
    (h : a ⊆ c) (k : b ⊆ d) : Extends (view line a b) (view line c d) := by
  have go {p q : Finset (Fin n)} (inc : p ⊆ q) : ∀ i, mask p i=true → mask q i=true :=
    fun i hi => decide_eq_true (inc (of_decide_eq_true hi))
  cases line
  · exact ⟨go h,go k⟩
  · exact ⟨go k,go h⟩

theorem off {s t u : Finset (Fin n)} (line : Bool) (x : Fin n)
    (same : ∀ i ≠ x, i ∈ s ↔ i ∈ u) : AgreeOff line x (view line s t) (view line u t) := by
  have eq : ∀ i ≠ x, mask s i = mask u i := fun i ne => by simp only [mask,same i ne]
  cases line <;> exact ⟨rfl,eq⟩

/-- Each other owner blocks at most one neighbor of x. -/
theorem escape (N : Fin n → Finset (Fin n)) (x : Fin n) (s : Finset (Fin n))
    (absent : x ∉ s) (big : s.card < (N x).card)
    (overlap : ∀ i ≠ x, (N x ∩ N i).card ≤ 1) :
    ∃ y ∈ N x, ∀ i ∈ s, y ∉ N i := by
  let blocked := s.biUnion (fun i => N x ∩ N i)
  have small : blocked.card ≤ s.card := by
    simpa [blocked] using Finset.card_biUnion_le_card_mul s (fun i => N x ∩ N i) 1
      (fun i hi => overlap i (fun eq => absent (eq ▸ hi)))
  have missing : ¬ N x ⊆ blocked := fun h => (Nat.not_le_of_gt big) ((Finset.card_le_card h).trans small)
  obtain ⟨y,hy,out⟩ := Finset.not_subset.mp missing
  exact ⟨y,hy,fun i hi h => out (Finset.mem_biUnion.mpr ⟨i,hi,Finset.mem_inter.mpr ⟨hy,h⟩⟩)⟩

theorem safe (C : Circuit n) (line : Bool) (x : Fin n) (sib : Nat)
    (good : sib<n+n+C.size) (shield : Shield C line x sib)
    (N : Fin n → Finset (Fin n)) (s t : Finset (Fin n))
    (avoid : ∀ i ∈ s, ∀ j ∈ t, j ∉ N i)
    (big : s.card < (N x).card) (overlap : ∀ i ≠ x, (N x ∩ N i).card ≤ 1)
    (positive : ∀ y ∈ N x, view line {x} {y} ∈ C.wire C.output)
    (negative : ∀ y ∈ N x, (∀ i ∈ s.erase x, ∀ j ∈ insert y t, j ∉ N i) →
        view line (s.erase x) (insert y t) ∉ C.wire C.output) :
    view line s t ∉ C.wire sib := by
  intro hit
  let clean := s.erase x
  obtain ⟨y,hy,free⟩ := escape N x clean (Finset.notMem_erase _ _)
    ((Finset.card_le_card (Finset.erase_subset x s)).trans_lt big) overlap
  have oldAgree := off (t := t) (s := s) (u := clean) line x (fun i ne => by simp [clean,ne])
  have oldHit := (shield _ _ oldAgree).1.mp hit
  let ext := insert y t
  have grow : view line clean ext ∈ C.wire sib :=
    wire_up C sib good (view_mono line (fun _ h => h) (Finset.subset_insert y t)) oldHit
  have flip := off (t := ext) (s := clean) (u := insert x clean) line x (fun i ne => by simp [ne])
  have pos : view line (insert x clean) ext ∈ C.wire C.output :=
    wire_up C _ C.output_lt (view_mono line (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))
      (Finset.singleton_subset_iff.mpr (Finset.mem_insert_self _ _))) (positive y hy)
  apply negative y hy _ ((shield _ _ flip).2 grow |>.mpr pos)
  intro i hi j hj
  rcases Finset.mem_insert.mp hj with rfl | h
  · exact free i hi
  · exact avoid i (Finset.mem_erase.mp hi).2 j h

theorem mask_single (i : Fin n) : mask {i} = single i := by
  funext j
  simp [mask,single]

variable (C : Circuit n) (I : Fin n → Fin n → Prop) [DecidableRel I]
variable (degree : ∀ l, Fintype.card {p // I p l} = 401+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 2)

include degree unique pos neg in
theorem line_safe (x : Fin n) (sib : Nat) (good : sib<n+n+C.size) (shield : Shield C true x sib)
    (a b : Fin n → Bool) (lb : Fintype.card {l // b l=true} ≤ 2)
    (ind : ∀ p l, a p=true → b l=true → ¬ I p l) : (a,b) ∉ C.wire sib := by
  let N := IncidenceRobust.points I
  let s := active b
  let t := active a
  have cs : s.card ≤ 2 := (count_active b).trans_le lb
  have test : view true s t = (a,b) := by simp [view,s,t,mask_active]
  rw [← test]
  apply safe C true x sib good shield N s t
  · intro i hi j hj hy
    exact ind j i (by simpa [t,active] using hj) (by simpa [s,active] using hi)
      ((Finset.mem_filter.mp hy).2)
  · have big := IncidenceRobust.points_card I degree x
    change s.card < (IncidenceRobust.points I x).card
    omega
  · exact fun i ne => IncidenceRobust.point_overlap I unique ne.symm
  · intro y hy
    simpa [view,mask_single] using pos y x (Finset.mem_filter.mp hy).2
  · intro y _ independent
    apply neg
    · rw [count_mask]
      simpa using (Finset.card_le_univ (insert y t))
    · rw [count_mask]
      exact (Finset.card_le_card (Finset.erase_subset x s)).trans cs
    · intro p l hp hl inc
      exact independent l (of_decide_eq_true hl) p (of_decide_eq_true hp)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩)

theorem witness_neg (neg : negatives C I n 2) (line : Bool) (x : Fin n) :
    witness line x ∉ C.wire C.output := by
  have one : Fintype.card {j // single x j=true} ≤ 1 := by
    let f : {j // single x j=true} → Unit := fun _ => ()
    have h : Function.Injective f := by
      intro a b _
      apply Subtype.ext
      exact (of_decide_eq_true a.property).trans (of_decide_eq_true b.property).symm
    simpa using Fintype.card_le_of_injective f h
  cases line
  · apply neg
    · exact (Fintype.card_subtype_le _).trans_eq (Fintype.card_fin n)
    · simp
    · simp
  · apply neg
    · simp
    · omega
    · simp

theorem selected_shield (neg : negatives C I n 2)
    {line : Bool} {j : ℕ} {b : Bool} (h : select C line j=some b) :
    ∃ x : Fin n, (C.code j).op=.join ∧ j<C.size ∧
      Shield C line x (other (C.code j) b) := by
  obtain ⟨x,hx⟩ := selected_mem C h
  exact ⟨x,walk_shields C (IncidencePinHoistSparse.witness_neg C I neg line x) _ _ _
    (initial C _ _ (owner_hot C line x)) (j,b) hx⟩


include degree unique pos neg in
theorem selected {j : Nat} {b : Bool} (h : select C true j = some b) :
    ∃ x : Fin n, (C.code j).op=.join ∧ j<C.size ∧ Shield C true x (other (C.code j) b) ∧
      ∀ a d : Fin n → Bool, Fintype.card {l // d l=true} ≤ 2 →
        (∀ p l, a p=true → d l=true → ¬ I p l) → (a,d) ∉ C.wire (other (C.code j) b) := by
  obtain ⟨x,op,hj,sh⟩ := selected_shield C I neg h
  have ⟨hl,hr⟩ := C.earlier j hj
  have bound : other (C.code j) b < n+n+C.size := by
    cases b <;> simp only [other,Bool.false_eq_true,if_true,if_false] <;> omega
  exact ⟨x,op,hj,sh,line_safe C I degree unique pos neg x _ bound sh⟩

include degree unique pos neg in
theorem pure_point {j : Nat} {b : Bool} (h : select C true j = some b) (p : Fin n) :
    witness false p ∉ C.wire (other (C.code j) b) := by
  obtain ⟨_,_,_,_,cold⟩ := selected C I degree unique pos neg h
  exact cold (single p) (fun _ => false) (by simp) (by simp)
private theorem agree_raw (line : Bool) (x : Fin n) (u v : Input n) (agr : AgreeOff line x u v)
    (i : Nat) (hi : i<n+n) (ne : i ≠ owner line x) : u∈C.wire i ↔ v∈C.wire i := by
  by_cases lo : i<n
  · let j : Fin n := ⟨i,lo⟩
    rw [(C.inputs j).1]
    cases line
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.2 j (fun eq => ne (congrArg Fin.val eq))]
    · change u.1 j=true ↔ v.1 j=true
      rw [agr.1]
  · let j : Fin n := ⟨i-n,by omega⟩
    have form : i=n+j.val := by dsimp [j]; omega
    rw [form,(C.inputs j).2]
    cases line
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.1]
    · change u.2 j=true ↔ v.2 j=true
      rw [agr.2 j (by intro eq; apply ne; change i=n+x.val; rw [← eq]; exact form)]

private theorem no_escape (line : Bool) (x : Fin n) {w : Nat} {H : Finset Nat}
    (p : Prefix C (owner line x) w H (witness line x)) (dead : uses C w = 0)
    (u v : Input n) (agr : AgreeOff line x u v) :
    ∀ i<n+n+C.size, i∉H → (u∈C.wire i ↔ v∈C.wire i) := by
  have empty : occurrences C w = [] :=
    List.length_eq_zero_iff.mp ((occurrence_count C w).trans dead)
  have parent (j : Nat) (hj : j<C.size) (b : Bool) (outside : n+n+j∉H) :
      keep (C.code j) b ∉ H := by
    intro h
    have eq := (p.leaves j hj b h).resolve_right outside
    have mem := (occurrence_mem C w j b).mpr ⟨hj,eq⟩
    rw [empty] at mem
    exact List.not_mem_nil mem
  intro i
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    intro good outside
    by_cases raw : i<n+n
    · exact agree_raw C line x u v agr i raw (fun eq => outside (eq ▸ p.ownerInside))
    let j := i-(n+n)
    have atGate : i=n+n+j := by dsimp [j]; omega
    have valid : j<C.size := by omega
    obtain ⟨hl,hr⟩ := C.earlier j valid
    have l := ih (C.code j).left (by omega) (by omega) (parent j valid true (atGate ▸ outside))
    have r := ih (C.code j).right (by omega) (by omega) (parent j valid false (atGate ▸ outside))
    rw [atGate,C.law j valid]
    cases op : (C.code j).op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto

theorem exit_used_of_neighbor (neg : negatives C I n 2) (pos : flags C I) (line : Bool)
    (x y : Fin n) (inc : if line then I y x else I x y) {w : Nat} {H : Finset Nat}
    (p : Prefix C (owner line x) w H (witness line x)) : 0 < uses C w := by
  by_contra! dead
  have zero : uses C w=0 := by omega
  have out : C.output∉H := fun h => IncidencePinHoistSparse.witness_neg C I neg line x (p.hot _ h)
  cases line
  · let u : Input n := (single x,single y)
    have agree : AgreeOff false x u (witness true y) := by
      refine ⟨rfl,?_⟩
      intro i ne
      simp [u,witness,single,ne]
    have same := no_escape C false x p zero _ _ agree C.output C.output_lt out
    exact IncidencePinHoistSparse.witness_neg C I neg true y (same.mp (pos x y inc))
  · let u : Input n := (single y,single x)
    have agree : AgreeOff true x u (witness false y) := by
      refine ⟨rfl,?_⟩
      intro i ne
      simp [u,witness,single,ne]
    have same := no_escape C true x p zero _ _ agree C.output C.output_lt out
    exact IncidencePinHoistSparse.witness_neg C I neg false y (same.mp (pos y x inc))


include degree pos neg in
theorem line_exit_used (x : Fin n) {w : Nat} {H : Finset Nat}
    (p : Prefix C (owner true x) w H (witness true x)) : 0 < uses C w := by
  obtain ⟨y,hy⟩ := Finset.card_pos.mp (show 0 < (IncidenceRobust.points I x).card by
    rw [IncidenceRobust.points_card I degree]; decide)
  exact exit_used_of_neighbor C I neg pos true x y (Finset.mem_filter.mp hy).2 p

#print axioms selected
#print axioms pure_point
#print axioms line_exit_used
end IncidencePinHoistSparse
