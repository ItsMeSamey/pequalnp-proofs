import IncidenceStartNormalization
import Research.IncidenceRobust
import Mathlib.Algebra.Order.BigOperators.Group.Finset

namespace IncidenceHoistSparse
open SparseIncidence CircuitRewire IncidenceStartNormalization
variable {n : Nat}

def AgreeOff (line : Bool) (x : Fin n) (u v : Input n) : Prop :=
  if line then u.1 = v.1 ∧ ∀ j ≠ x, u.2 j = v.2 j
  else u.2 = v.2 ∧ ∀ j ≠ x, u.1 j = v.1 j

/-- A sibling is insensitive to the raw flip. Once it is true the exit
shields the output from that same flip. All values are actual circuit wires. -/
def Shield (C : Circuit n) (line : Bool) (x : Fin n) (sib : Nat) : Prop :=
  ∀ u v, AgreeOff line x u v →
    (u ∈ C.wire sib ↔ v ∈ C.wire sib) ∧
    (u ∈ C.wire sib → (u ∈ C.wire C.output ↔ v ∈ C.wire C.output))

private theorem eval_up (g : Gate) {X : Nat → Set (Input n)}
    (l : Upward (X g.left)) (r : Upward (X g.right)) : Upward (g.eval X) := by
  rcases g with ⟨op,lid,rid⟩
  cases op <;> simp only [Gate.eval,Op.eval] at * <;>
    intro u v ext hm
  · exact hm.elim (fun h => Or.inl (l ext h)) (fun h => Or.inr (r ext h))
  · exact ⟨l ext hm.1,r ext hm.2⟩
  · exact l ext hm
  · exact hm.elim

theorem wire_up (C : Circuit n) (i : Nat) (valid : i < n+n+C.size) : Upward (C.wire i) := by
  induction i using Nat.strong_induction_on with
  | ind i ih =>
    by_cases lo : i<n
    · rw [(C.inputs ⟨i,lo⟩).1]
      exact fun _ _ ext h => ext.1 _ h
    by_cases raw : i<n+n
    · let k : Fin n := ⟨i-n,by omega⟩
      have eq : i=n+k.val := by dsimp [k]; omega
      rw [eq,(C.inputs k).2]
      exact fun _ _ ext h => ext.2 _ h
    let j := i-(n+n)
    have eq : i=n+n+j := by dsimp [j]; omega
    have inside : j<C.size := by omega
    obtain ⟨hl,hr⟩ := C.earlier j inside
    rw [eq,C.law j inside]
    exact eval_up _ (ih _ (by omega) (by omega)) (ih _ (by omega) (by omega))

private def mask (s : Finset (Fin n)) : Fin n → Bool := fun i => decide (i ∈ s)
private def active (a : Fin n → Bool) := Finset.univ.filter (fun i => a i = true)
private theorem mask_active (a : Fin n → Bool) : mask (active a) = a := by
  funext i
  simp [mask,active]
private theorem count_mask (s : Finset (Fin n)) :
    Fintype.card {i // mask s i = true} = s.card := by
  simp [Fintype.card_subtype,mask]
private theorem count_active (a : Fin n → Bool) :
    (active a).card = Fintype.card {i // a i = true} := by
  rw [← count_mask,mask_active]

private def view (line : Bool) (s t : Finset (Fin n)) : Input n :=
  if line then (mask t,mask s) else (mask s,mask t)

private theorem view_mono (line : Bool) {a b c d : Finset (Fin n)}
    (h : a ⊆ c) (k : b ⊆ d) : Extends (view line a b) (view line c d) := by
  have go {p q : Finset (Fin n)} (inc : p ⊆ q) : ∀ i, mask p i=true → mask q i=true :=
    fun i hi => decide_eq_true (inc (of_decide_eq_true hi))
  cases line
  · exact ⟨go h,go k⟩
  · exact ⟨go k,go h⟩

private theorem off {s t u : Finset (Fin n)} (line : Bool) (x : Fin n)
    (same : ∀ i ≠ x, i ∈ s ↔ i ∈ u) : AgreeOff line x (view line s t) (view line u t) := by
  have eq : ∀ i ≠ x, mask s i = mask u i := fun i ne => by simp only [mask,same i ne]
  cases line <;> exact ⟨rfl,eq⟩

/-- Each other owner blocks at most one neighbor of x. -/
private theorem escape (N : Fin n → Finset (Fin n)) (x : Fin n) (s : Finset (Fin n))
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

private theorem safe (C : Circuit n) (line : Bool) (x : Fin n) (sib : Nat)
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

private theorem mask_single (i : Fin n) : mask {i} = single i := by
  funext j
  simp [mask,single]

variable (C : Circuit n) (I : Fin n → Fin n → Prop) [DecidableRel I]
variable (degree : ∀ l, Fintype.card {p // I p l} = 401+1)
variable (unique : ∀ a b, a ≠ b → ∃! l, I a l ∧ I b l)
variable (pos : flags C I) (neg : negatives C I n 401)

include degree unique pos neg in
theorem line_safe (x : Fin n) (sib : Nat) (good : sib<n+n+C.size) (shield : Shield C true x sib)
    (a b : Fin n → Bool) (lb : Fintype.card {l // b l=true} ≤ 401)
    (ind : ∀ p l, a p=true → b l=true → ¬ I p l) : (a,b) ∉ C.wire sib := by
  let N := IncidenceRobust.points I
  let s := active b
  let t := active a
  have cs : s.card ≤ 401 := (count_active b).trans_le lb
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

include degree unique pos neg in
theorem point_safe (hn : n=401^2+401+1) (x : Fin n) (sib : Nat) (good : sib<n+n+C.size)
    (shield : Shield C false x sib) (a b : Fin n → Bool)
    (pa : Fintype.card {p // a p=true} ≤ 401) (lb : Fintype.card {l // b l=true} ≤ 400)
    (ind : ∀ p l, a p=true → b l=true → ¬ I p l) : (a,b) ∉ C.wire sib := by
  let N := IncidenceRobust.lines I
  let s := active a
  let t := active b
  have cs : s.card ≤ 401 := (count_active a).trans_le pa
  have ct : t.card ≤ 400 := (count_active b).trans_le lb
  have test : view false s t = (a,b) := by simp [view,s,t,mask_active]
  rw [← test]
  apply safe C false x sib good shield N s t
  · intro i hi j hj hy
    exact ind i j (by simpa [s,active] using hi) (by simpa [t,active] using hj)
      ((Finset.mem_filter.mp hy).2)
  · have big := IncidenceRobust.lines_card I degree unique (by decide : 0 < 401) hn x
    change s.card < (IncidenceRobust.lines I x).card
    omega
  · exact fun i ne => IncidenceRobust.line_overlap I unique ne.symm
  · intro y hy
    simpa [view,mask_single] using pos x y (Finset.mem_filter.mp hy).2
  · intro y _ independent
    apply neg
    · rw [count_mask]
      simpa using (Finset.card_le_univ (s.erase x))
    · rw [count_mask]
      exact (Finset.card_insert_le y t).trans (by omega)
    · intro p l hp hl inc
      exact independent p (of_decide_eq_true hp) l (of_decide_eq_true hl)
        (Finset.mem_filter.mpr ⟨Finset.mem_univ _,inc⟩)

#print axioms line_safe
#print axioms point_safe
end IncidenceHoistSparse
