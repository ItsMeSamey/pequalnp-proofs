import PEqualNP.Defs


namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

def live : List Gate → ℕ → ℕ → Finset ℕ
  | [], n, o => if o < n then {o} else ∅
  | g :: gs, n, o =>
    let t := live gs (n+1) o
    if n ∈ t then (t.erase n) ∪ (g.inputs.toFinset.filter (· < n)) else t

theorem live_lt (gs : List Gate) (n o : ℕ) :
    ∀ i ∈ live gs n o, i < n := by
  induction gs generalizing n with
  | nil =>
    intro i hi
    by_cases h : o < n <;> simp_all [live]
  | cons g gs ih =>
    intro i hi
    by_cases h : n ∈ live gs (n+1) o
    · simp only [live, ite_eq_left h, Finset.mem_union, Finset.mem_erase, Finset.mem_filter] at hi
      rcases hi with ⟨hne, hi⟩ | ⟨_, hi⟩
      · have := ih (n+1) i hi
        omega
      · exact hi
    · simp only [live, ite_eq_right h] at hi
      have := ih (n+1) i hi
      by_contra hn
      have : i = n := by omega
      exact h (this ▸ hi)

theorem live_card (gs : List Gate) (n o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) : (live gs n o).card ≤ gs.length + 1 := by
  induction gs generalizing n with
  | nil => by_cases ho : o < n <;> simp [live, ho]
  | cons g gs ih =>
    have ht := ih (n+1) (fun g hg => h g (List.mem_cons_of_mem _ hg))
    have hg := h g (List.mem_cons_self ..)
    by_cases he : n ∈ live gs (n+1) o
    · simp only [live, ite_eq_left he, List.length_cons]
      have hu := Finset.card_union_le ((live gs (n+1) o).erase n)
        (g.inputs.toFinset.filter (· < n))
      have hz := Finset.card_erase_add_one he
      have hf := Finset.card_le_card (Finset.filter_subset (· < n) g.inputs.toFinset)
      have hl := List.toFinset_card_le g.inputs
      omega
    · simp only [live, ite_eq_right he, List.length_cons]
      omega

def advance (g : Gate) (w : List Bool) : List Bool :=
  w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]

theorem getD_missing {x : List Bool} {i : ℕ} (h : x.length ≤ i) :
    x.getD i false = false := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem getD_advance_lt (g : Gate) (x : List Bool) (i : ℕ) (h : i < x.length) :
    (advance g x).getD i false = x.getD i false := by
  simp [advance, List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_advance_eq (g : Gate) (x : List Bool) :
    (advance g x).getD x.length false = g.op.eval (g.inputs.map fun i => x.getD i false) := by
  simp [advance, List.getD_eq_getElem?_getD]

theorem advance_len (g : Gate) (x : List Bool) :
    (advance g x).length = x.length + 1 := by simp [advance]

end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds

/-- Each reverse step expands one demanded output into two distinct earlier
inputs, both absent from the surviving demands. -/
def freshBinarySweep : List Gate → ℕ → ℕ → Prop
  | [], n, o => o < n
  | g :: gs, n, o =>
    let tail := live gs (n + 1) o
    n ∈ tail ∧ g.inputs.length = 2 ∧ g.inputs.Nodup ∧
      (∀ i ∈ g.inputs, i < n) ∧ Disjoint (tail.erase n) g.inputs.toFinset ∧
      freshBinarySweep gs (n + 1) o

theorem freshBinarySweep_of_max (gs : List Gate) (n o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2)
    (eq : (live gs n o).card = gs.length + 1) : freshBinarySweep gs n o := by
  induction gs generalizing n with
  | nil =>
    change o < n
    by_contra hn
    simp [live, hn] at eq
  | cons g gs ih =>
    let t := live gs (n + 1) o
    let a := g.inputs.toFinset.filter (· < n)
    have hgs : ∀ g ∈ gs, g.inputs.length ≤ 2 := fun k hk => h k (List.mem_cons_of_mem _ hk)
    have ht : t.card ≤ gs.length + 1 := live_card gs (n+1) o hgs
    have hg := h g (List.mem_cons_self ..)
    have he : n ∈ t := by
      by_contra hn
      change n ∉ live gs (n+1) o at hn
      simp only [live, ite_eq_right hn, List.length_cons] at eq
      change t.card = gs.length + 1 + 1 at eq
      omega
    have hu : ((t.erase n) ∪ a).card = gs.length + 1 + 1 := by
      simpa only [live, ite_eq_left he, List.length_cons, t, a] using eq
    have hc := Finset.card_union_le (t.erase n) a
    have hz := Finset.card_erase_add_one he
    have ha : a ⊆ g.inputs.toFinset := Finset.filter_subset _ _
    have hf := Finset.card_le_card ha
    have hl := List.toFinset_card_le g.inputs
    have full : a = g.inputs.toFinset := Finset.eq_of_subset_of_card_le ha (by omega)
    have nd : g.inputs.Nodup := by
      change (g.inputs : Multiset ℕ).Nodup
      apply Multiset.toFinset_card_eq_card_iff_nodup.mp
      change g.inputs.toFinset.card = g.inputs.length
      omega
    refine ⟨he, by omega, nd, ?_, ?_, ih (n := n+1) hgs (by change t.card = _; omega)⟩
    · intro i hi
      have hm : i ∈ a := full.symm ▸ (List.mem_toFinset.mpr hi)
      exact (Finset.mem_filter.mp hm).2
    · rw [← full]
      apply Finset.card_union_eq_card_add_card.mp
      change ((t.erase n) ∪ a).card = (t.erase n).card + a.card
      omega

end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem eval_mono_live (C : Circuit) (n : ℕ) (x y : List Bool) (hm : Monotone2 C)
    (hx : x.length = n) (hy : y.length = n)
    (h : ∀ i ∈ live C.gates n C.output, x.getD i false = true → y.getD i false = true) :
    C.eval x = true → C.eval y = true := by
  obtain ⟨gs,o⟩ := C
  induction gs generalizing n x y with
  | nil =>
    change x.getD o false = true → y.getD o false = true
    by_cases ho : o < n
    · exact h o (by simp [live, ho])
    · rw [getD_missing (by omega : x.length ≤ o)]
      simp
  | cons g gs ih =>
    change (Circuit.mk gs o).eval (advance g x) = true → (Circuit.mk gs o).eval (advance g y) = true
    apply ih (n+1) (advance g x) (advance g y)
      (by simp [advance,hx]) (by simp [advance,hy]) (fun a ha => hm a (List.mem_cons_of_mem _ ha))
    intro i hi
    have hlt := live_lt gs (n+1) o i hi
    by_cases he : i = n
    · subst i
      rw [show (advance g x).getD n false = _ by simpa only [hx] using getD_advance_eq g x]
      rw [show (advance g y).getD n false = _ by simpa only [hy] using getD_advance_eq g y]
      have inj : ∀ j ∈ g.inputs, x.getD j false = true → y.getD j false = true := by
        intro j hj
        by_cases hjn : j < n
        · exact h j (by simp [live, hi, hj, hjn])
        · rw [getD_missing (by omega : x.length ≤ j)]
          simp
      have hg : g.op = .and ∨ g.op = .or := (hm g (List.mem_cons_self ..)).1
      rcases hg with hg | hg
      · simp only [hg, GateOp.eval, List.all_eq_true, List.mem_map, id_eq]
        rintro ha _ ⟨j,hj,rfl⟩
        exact inj j hj (ha _ ⟨j,hj,rfl⟩)
      · simp only [hg, GateOp.eval, List.any_eq_true, List.mem_map, id_eq]
        rintro ⟨_, ⟨j,hj,rfl⟩, ha⟩
        exact ⟨_, ⟨j,hj,rfl⟩, inj j hj ha⟩
    · rw [getD_advance_lt _ _ _ (by omega), getD_advance_lt _ _ _ (by omega)]
      apply h i
      by_cases hn : n ∈ live gs (n+1) o <;> simp [live, hn, he, hi]
end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds

def isOrGate (g : Gate) : Bool :=
  match g.op with
  | .or => true
  | _ => false

def falseParents (g : Gate) (w : List Bool) : Finset ℕ :=
  match g.op with
  | .or => g.inputs.toFinset.filter (· < w.length)
  | .and => match g.inputs.find? (fun i => !(w.getD i false)) with
    | some i => if i < w.length then {i} else ∅
    | none => ∅
  | _ => ∅

def falseLive : List Gate → List Bool → ℕ → Finset ℕ
  | [], w, o => if o < w.length ∧ w.getD o false = false then {o} else ∅
  | g :: gs, w, o =>
    let t := falseLive gs (advance g w) o
    if w.length ∈ t then (t.erase w.length) ∪ falseParents g w else t

theorem falseParents_lt (g : Gate) (w : List Bool) (i : ℕ)
    (hi : i ∈ falseParents g w) : i < w.length := by
  cases h : g.op <;> simp [falseParents, h] at hi
  · split at hi
    · split at hi <;> simp_all
    · simp at hi
  · exact hi.2

theorem falseLive_lt (gs : List Gate) (w : List Bool) (o i : ℕ)
    (hi : i ∈ falseLive gs w o) : i < w.length := by
  induction gs generalizing w with
  | nil =>
    simp only [falseLive] at hi
    split at hi <;> simp_all
  | cons g gs ih =>
    have len := advance_len g w
    by_cases hm : w.length ∈ falseLive gs (advance g w) o
    · simp only [falseLive, ite_eq_left hm, Finset.mem_union, Finset.mem_erase] at hi
      rcases hi with ⟨hne, hi⟩ | hi
      · have := ih (advance g w) hi
        omega
      · exact falseParents_lt g w i hi
    · simp only [falseLive, ite_eq_right hm] at hi
      have := ih (advance g w) hi
      by_contra hn
      have he : i = w.length := by omega
      exact hm (he ▸ hi)

theorem falseParents_card (g : Gate) (w : List Bool) (h : g.inputs.length ≤ 2) :
    (falseParents g w).card ≤ (if isOrGate g then 2 else 1) := by
  cases hop : g.op <;> simp [isOrGate, falseParents, hop]
  · split
    · split <;> simp
    · simp
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans ((List.toFinset_card_le _).trans h)

theorem falseLive_card (gs : List Gate) (w : List Bool) (o : ℕ)
    (h : ∀ g ∈ gs, g.inputs.length ≤ 2) :
    (falseLive gs w o).card ≤ (gs.filter isOrGate).length + 1 := by
  induction gs generalizing w with
  | nil =>
    simp only [falseLive, List.filter_nil, List.length_nil]
    split <;> simp
  | cons g gs ih =>
    let t := falseLive gs (advance g w) o
    have ht : t.card ≤ (gs.filter isOrGate).length + 1 :=
      ih (advance g w) (fun k hk => h k (List.mem_cons_of_mem _ hk))
    have hp := falseParents_card g w (h g (List.mem_cons_self ..))
    by_cases hm : w.length ∈ t
    · have he := Finset.card_erase_add_one hm
      have hu := Finset.card_union_le (t.erase w.length) (falseParents g w)
      change ((if w.length ∈ t then t.erase w.length ∪ falseParents g w else t).card) ≤ _
      rw [ite_eq_left hm]
      cases hb : isOrGate g <;> simp [hb] at hp ⊢ <;> omega
    · change ((if w.length ∈ t then t.erase w.length ∪ falseParents g w else t).card) ≤ _
      rw [ite_eq_right hm]
      cases hb : isOrGate g <;> simp [hb] <;> omega

end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity

theorem falseParents_semantic (g : Gate) (x y : List Bool) (hlen : y.length = x.length)
    (op : g.op = .and ∨ g.op = .or)
    (agree : ∀ i ∈ falseParents g x, x.getD i false = false → y.getD i false = false)
    (hx : g.op.eval (g.inputs.map fun i => x.getD i false) = false) :
    g.op.eval (g.inputs.map fun i => y.getD i false) = false := by
  rcases op with hand | hor
  · rw [hand] at hx ⊢
    cases he : g.inputs.find? (fun i => !(x.getD i false)) with
    | none =>
      have hall := List.find?_eq_none.mp he
      have : GateOp.and.eval (g.inputs.map fun i => x.getD i false) = true := by
        simp only [GateOp.eval, List.all_map, List.all_eq_true]
        intro i hi
        simpa using hall i hi
      simp_all
    | some i =>
      have hi := List.mem_of_find?_eq_some he
      have hfx : x.getD i false = false := by simpa using List.find?_some he
      have hfy : y.getD i false = false := by
        by_cases hb : i < x.length
        · apply agree i _ hfx
          simp only [falseParents, hand, he, ite_eq_left hb, Finset.mem_singleton]
        · exact getD_missing (by omega)
      have hmem : false ∈ g.inputs.map (fun i => y.getD i false) :=
        List.mem_map.mpr ⟨i,hi,hfy⟩
      simpa [GateOp.eval, List.all_eq_false] using hmem
  · rw [hor] at hx ⊢
    simp only [GateOp.eval, List.any_map, List.any_eq_false] at hx ⊢
    intro i hi
    have hfx : x.getD i false = false := by simpa using hx i hi
    by_cases hb : i < x.length
    · have hfy := agree i (by simp [falseParents, hor, hi, hb]) hfx
      simpa using hfy
    · have hfy := getD_missing (by omega : y.length ≤ i)
      simpa using hfy

theorem falseLive_semantic (C : Circuit) (x y : List Bool)
    (hm : Monotone2 C) (hlen : y.length = x.length)
    (agree : ∀ i ∈ falseLive C.gates x C.output, x.getD i false = false → y.getD i false = false) :
    C.eval x = false → C.eval y = false := by
  obtain ⟨gs,o⟩ := C
  induction gs generalizing x y with
  | nil =>
    change x.getD o false = false → y.getD o false = false
    intro hf
    by_cases hb : o < x.length
    · exact agree o (by change o ∈ falseLive [] x o; simp only [falseLive, ite_eq_left (And.intro hb hf), Finset.mem_singleton]) hf
    · exact getD_missing (by omega)
  | cons g gs ih =>
    change (Circuit.mk gs o).eval (advance g x) = false → (Circuit.mk gs o).eval (advance g y) = false
    apply ih (advance g x) (advance g y) (by simp [advance, hlen])
      (fun a ha => hm a (List.mem_cons_of_mem _ ha))
    intro i hi hfx
    have hlt := falseLive_lt gs (advance g x) o i hi
    rw [advance_len] at hlt
    by_cases he : i = x.length
    · subst i
      rw [getD_advance_eq] at hfx
      rw [← hlen, getD_advance_eq]
      apply falseParents_semantic g x y hlen (hm g (List.mem_cons_self ..)).1 _ hfx
      intro j hj
      exact agree j (by simp [falseLive, hi, hj])
    · have hb : i < x.length := by omega
      rw [getD_advance_lt _ _ _ hb] at hfx
      rw [getD_advance_lt _ _ _ (by omega)]
      apply agree i _ hfx
      by_cases hn : x.length ∈ falseLive gs (advance g x) o <;> simp [falseLive, hn, hi, he]
end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.Represents

private theorem left_change {n m : ℕ} (u w : Fin n) (v : Fin m) (i : ℕ)
    (hi : i ≠ u.val) (h : (oneEach u v).getD i false = true) :
    (oneEach w v).getD i false = true := by
  by_cases hn : i < n
  · have hne : (⟨i, hn⟩ : Fin n) ≠ u := fun he => hi (congrArg Fin.val he)
    simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hn, hne] at h
  · simpa [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.le_of_not_gt hn] using h

private theorem right_change {n m : ℕ} (u : Fin n) (v w : Fin m) (i : ℕ)
    (hi : i ≠ n + v.val) (h : (oneEach u v).getD i false = true) :
    (oneEach u w).getD i false = true := by
  by_cases hn : i < n
  · simpa [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_left, hn] using h
  · by_cases hm : i-n < m
    · have hne : (⟨i-n, hm⟩ : Fin m) ≠ v := by
        intro he
        have := congrArg Fin.val he
        simp at this
        omega
      simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.le_of_not_gt hn, hm, hne] at h
    · simp [oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right, Nat.le_of_not_gt hn, hm] at h

theorem mixed_support {n m : ℕ} (A : Fin n → Fin m → Bool) (S : Finset ℕ)
    (R : Finset (Fin n)) (K : Finset (Fin m))
    (hr : ∀ u ∈ R, ∃ v w, A u v = true ∧ A w v = false)
    (hk : ∀ v ∈ K, ∃ u w, A u v = true ∧ A u w = false)
    (mono : ∀ u v w z, (∀ i ∈ S, (oneEach u v).getD i false = true →
      (oneEach w z).getD i false = true) → A u v = true → A w z = true) :
    R.card + K.card ≤ S.card := by
  let e : Fin n ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
  let f : Fin m ↪ ℕ := ⟨fun j => n+j.val, fun a b h => Fin.ext (Nat.add_left_cancel h)⟩
  have hR : R.map e ⊆ S := by
    intro i hi
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨v,w,ht,hf⟩ := hr u hu
    by_contra miss
    change u.val ∉ S at miss
    have := mono u v w v (fun j hj => left_change u w v j (fun h => miss (h ▸ hj))) ht
    simp_all
  have hK : K.map f ⊆ S := by
    intro i hi
    obtain ⟨v, hv, rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨u,w,ht,hf⟩ := hk v hv
    by_contra miss
    change n+v.val ∉ S at miss
    have := mono u v u w (fun j hj => right_change u v w j (fun h => miss (h ▸ hj))) ht
    simp_all
  have hd : Disjoint (R.map e) (K.map f) := by
    apply Finset.disjoint_left.mpr
    intro i hi hk
    obtain ⟨u,_,rfl⟩ := Finset.mem_map.mp hi
    obtain ⟨v,_,h⟩ := Finset.mem_map.mp hk
    change n+v.val = u.val at h
    omega
  simpa [Finset.card_union_of_disjoint hd] using Finset.card_le_card (Finset.union_subset hR hK)

end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.Represents

theorem missingCell_bound {n m : ℕ} (i : Fin n) (j : Fin m) (S : Finset ℕ)
    (cert : ∀ u v, (u ≠ i ∨ v ≠ j) → ∃ k ∈ S,
      (oneEach u v).getD k false = true ∧ (oneEach i j).getD k false = false) :
    (n - 1) + (m - 1) ≤ S.card := by
  let A : Fin n → Fin m → Bool := fun u v => decide (u ≠ i ∨ v ≠ j)
  have h := mixed_support A S (Finset.univ.erase i) (Finset.univ.erase j)
    (by
      intro u hu
      exact ⟨j, i, by simp [A, (Finset.mem_erase.mp hu).1], by simp [A]⟩)
    (by
      intro v hv
      exact ⟨i, j, by simp [A, (Finset.mem_erase.mp hv).1], by simp [A]⟩)
    (by
      intro u v w z hwire hpos
      by_cases hw : w = i
      · by_cases hz : z = j
        · subst w
          subst z
          obtain ⟨k, hk, htrue, hfalse⟩ := cert u v (of_decide_eq_true hpos)
          have hbad := hwire k hk htrue
          simp_all
        · simp [A, hz]
      · simp [A, hw])
  simpa [Finset.card_erase_of_mem] using h

theorem missingCell_bound_of_eval {n m : ℕ} (i : Fin n) (j : Fin m)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (S : Finset ℕ)
    (neg : C.eval (oneEach i j) = false)
    (pos : ∀ u v, (u ≠ i ∨ v ≠ j) → C.eval (oneEach u v) = true)
    (keep : ∀ (u : Fin n) (v : Fin m), (∀ k ∈ S, (oneEach i j).getD k false = false →
      (oneEach u v).getD k false = false) → C.eval (oneEach i j) = false →
      C.eval (oneEach u v) = false) : (n-1) + (m-1) ≤ S.card := by
  apply missingCell_bound i j S
  intro u v huv
  by_contra hnone
  have h := keep u v (by
    intro k hk hb
    cases ht : (oneEach u v).getD k false with
    | false => rfl
    | true => exact False.elim (hnone ⟨k, hk, ht, hb⟩)) neg
  rw [pos u v huv] at h
  contradiction

theorem missingCell_or_gate_bound {n m : ℕ} (i : Fin n) (j : Fin m)
    (C : PEqualNP.CircuitLowerBounds.Circuit) (hm : PEqualNP.MetaComplexity.Monotone2 C)
    (neg : C.eval (oneEach i j) = false)
    (pos : ∀ u v, (u ≠ i ∨ v ≠ j) → C.eval (oneEach u v) = true) :
    (n-1) + (m-1) ≤ (C.gates.filter isOrGate).length + 1 := by
  let S := falseLive C.gates (oneEach i j) C.output
  exact (missingCell_bound_of_eval i j C S neg pos (fun u v =>
    falseLive_semantic C (oneEach i j) (oneEach u v) hm (by simp [oneEach]))).trans
    (falseLive_card _ _ _ (fun g hg => (hm g hg).2))

end PEqualNP.Research.MissingCell

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

theorem missingCell_or_count {n m : ℕ} (i : Fin n) (j : Fin m) (C : Circuit)
    (hm : Monotone2 C)
    (hr : Represents (fun u v => !(decide (u = i) && decide (v = j))) C) :
    (n - 1) + (m - 1) ≤ (C.gates.filter isOrGate).length + 1 := by
  let S := falseLive C.gates (oneEach i j) C.output
  have lb := missingCell_bound_of_eval i j C S (by simp [hr i j])
    (by
      intro u v h
      rw [hr u v]
      rcases h with hu | hv <;> simp_all)
    (fun u v => falseLive_semantic C (oneEach i j) (oneEach u v) hm (by simp [oneEach]))
  exact lb.trans (falseLive_card C.gates (oneEach i j) C.output (fun g hg => (hm g hg).2))

theorem missingCell_optimal_gates {n m : ℕ} (i : Fin n) (j : Fin m) (C : Circuit)
    (hm : Monotone2 C)
    (hr : Represents (fun u v => !(decide (u = i) && decide (v = j))) C)
    (budget : C.size + 1 ≤ (n - 1) + (m - 1)) : ∀ g ∈ C.gates, g.op = .or := by
  have lo := missingCell_or_count i j C hm hr
  change C.gates.length + 1 ≤ _ at budget
  have hi := List.length_filter_le isOrGate C.gates
  have eqn : (C.gates.filter isOrGate).length = C.gates.length := by omega
  intro g hg
  have hor := List.length_filter_eq_length_iff.mp eqn g hg
  cases op : g.op <;> simp_all [isOrGate]
theorem missingCell_optimal_shape {n m : ℕ} (i : Fin n) (j : Fin m) (C : Circuit)
    (hm : Monotone2 C)
    (hr : Represents (fun u v => !(decide (u = i) && decide (v = j))) C)
    (budget : C.size + 1 ≤ (n - 1) + (m - 1)) :
    (∀ g ∈ C.gates, g.op = .or) ∧ freshBinarySweep C.gates (n+m) C.output := by
  refine ⟨missingCell_optimal_gates i j C hm hr budget, ?_⟩
  have lb := missingCell_bound_of_eval i j C (live C.gates (n+m) C.output) (by simp [hr i j])
    (by
      intro u v h
      rw [hr u v]
      rcases h with hu | hv <;> simp_all)
    (by
      intro u v keep hneg
      by_contra hn
      have hp : C.eval (oneEach u v) = true := by simpa using hn
      have hback := eval_mono_live C (n+m) (oneEach u v) (oneEach i j) hm
        (by simp [oneEach]) (by simp [oneEach]) (by
          intro k hk hkpos
          cases hb : (oneEach i j).getD k false with
          | false => exact Bool.noConfusion (hkpos.symm.trans (keep k hk hb))
          | true => rfl) hp
      simp_all)
  have hfan : ∀ g ∈ C.gates, g.inputs.length ≤ 2 := fun g hg => (hm g hg).2
  have hi := live_card C.gates (n+m) C.output hfan
  change C.gates.length + 1 ≤ _ at budget
  exact freshBinarySweep_of_max C.gates (n+m) C.output hfan (by omega)

end PEqualNP.Research.MissingCell


namespace OnePerShore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

/-- A row is charged exactly if a positive cell in it has a zero below it
in the same column. -/
def nonminimumRows {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin n) :=
  Finset.univ.filter fun u => ∃ v w, A u v = true ∧ A w v = false

/-- Column version of the same physical dependence test. -/
def nonminimumCols {n m : ℕ} (A : Fin n → Fin m → Bool) : Finset (Fin m) :=
  Finset.univ.filter fun v => ∃ u w, A u v = true ∧ A u w = false

def charged {n m : ℕ} (A : Fin n → Fin m → Bool) : ℕ :=
  (nonminimumRows A).card + (nonminimumCols A).card

theorem charged_le_live {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C) :
    charged A ≤ (live C.gates (n+m) C.output).card := by
  apply mixed_support A _ (nonminimumRows A) (nonminimumCols A)
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro v hv
    exact (Finset.mem_filter.mp hv).2
  · intro u v w z h ht
    rw [←rep w z]
    apply eval_mono_live C (n+m) (oneEach u v) (oneEach w z) legal
      (by simp [oneEach]) (by simp [oneEach]) h
    simpa [rep u v] using ht

theorem physical_size_floor {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (bound : RepSizeAtMost A s) : charged A - 1 ≤ s := by
  obtain ⟨C, legal, size, rep⟩ := bound
  have h := charged_le_live legal rep
  have cap := live_card C.gates (n+m) C.output (fun g hg => (legal g hg).2)
  change C.gates.length ≤ s at size
  omega

/-- At the dependence floor, no repeated use, invalid gate input, dead gate
or unary gate can remain in the demanded physical circuit. -/
theorem tight_physical_sweep {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C)
    (nonempty : 0 < charged A) (tight : C.size ≤ charged A - 1) :
    (live C.gates (n+m) C.output).card = charged A ∧
      C.size + 1 = charged A ∧ freshBinarySweep C.gates (n+m) C.output := by
  have h := charged_le_live legal rep
  have fan := fun g hg => (legal g hg).2
  have cap := live_card C.gates (n+m) C.output fan
  change C.gates.length ≤ charged A - 1 at tight
  change _ ∧ C.gates.length + 1 = _ ∧ _
  exact ⟨by omega, by omega, freshBinarySweep_of_max _ _ _ fan (by omega)⟩

end OnePerShore


namespace OnePerShore

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open PEqualNP.Research.MissingCell

inductive Formula where
  | atom (i : ℕ)
  | node (isAnd : Bool) (left right : Formula)

def Formula.leaves : Formula → List ℕ
  | .atom i => [i]
  | .node _ l r => l.leaves ++ r.leaves

def Formula.eval (x : ℕ → Bool) : Formula → Bool
  | .atom i => x i
  | .node op l r => if op then l.eval x && r.eval x else l.eval x || r.eval x

def Formula.bind (k : ℕ → Formula) : Formula → Formula
  | .atom i => k i
  | .node op l r => .node op (l.bind k) (r.bind k)

theorem Formula.bind_leaves (t : Formula) (k : ℕ → Formula) :
    (t.bind k).leaves = t.leaves.flatMap (fun i => (k i).leaves) := by
  induction t <;> simp_all [Formula.bind, Formula.leaves, List.flatMap_append]

theorem Formula.bind_eval (t : Formula) (k : ℕ → Formula) (x : ℕ → Bool) :
    (t.bind k).eval x = t.eval (fun i => (k i).eval x) := by
  induction t <;> simp_all [Formula.bind, Formula.eval]

private theorem two_inputs {l : List ℕ} (h : l.length = 2) : ∃ a b, l = [a,b] := by
  cases l with
  | nil => simp at h
  | cons a t =>
    cases t with
    | nil => simp at h
    | cons b t =>
      cases t with
      | nil => exact ⟨_,_,rfl⟩
      | cons c t => simp at h

theorem formula_of_sweep (gs : List Gate) (n o : ℕ)
    (legal : Monotone2 ⟨gs,o⟩) (sweep : freshBinarySweep gs n o) :
    ∃ t : Formula, t.leaves.Nodup ∧ t.leaves.toFinset = live gs n o ∧
      ∀ x : List Bool, x.length = n →
        t.eval (fun i => x.getD i false) = (Circuit.mk gs o).eval x := by
  induction gs generalizing n with
  | nil =>
    change o < n at sweep
    exact ⟨.atom o, by simp [Formula.leaves], by simp [Formula.leaves, live, sweep],
      fun _ _ => rfl⟩
  | cons g gs ih =>
    obtain ⟨used, len, distinct, earlier, fresh, tail⟩ := sweep
    obtain ⟨a,b,hargs⟩ := two_inputs len
    have hab : a ≠ b := by simpa [hargs] using distinct
    obtain ⟨t, nd, support, semantics⟩ :=
      ih (n+1) (fun k hk => legal k (List.mem_cons_of_mem _ hk)) tail
    let op := match g.op with | .and => true | _ => false
    let k (i : ℕ) : Formula := if i=n then .node op (.atom a) (.atom b) else .atom i
    have lk (i : ℕ) : (k i).leaves = if i=n then [a,b] else [i] := by
      by_cases h : i=n <;> simp [k,h,Formula.leaves]
    have away (i : ℕ) (hi : i ∈ t.leaves) (hn : i ≠ n) : i ≠ a ∧ i ≠ b := by
      have hs : i ∈ (live gs (n+1) o).erase n :=
        Finset.mem_erase.mpr ⟨hn, support ▸ List.mem_toFinset.mpr hi⟩
      have no := Finset.disjoint_left.mp fresh hs
      constructor <;> rintro rfl <;> exact no (by simp [hargs])
    refine ⟨t.bind k, ?_, ?_, ?_⟩
    · rw [Formula.bind_leaves, List.nodup_flatMap]
      refine ⟨fun i _ => ?_, nd.imp_of_mem ?_⟩
      · by_cases h : i=n <;> simp [lk,h,hab]
      · intro i j hi hj hij
        change List.Disjoint (k i).leaves (k j).leaves
        rw [lk,lk]
        by_cases hin : i=n <;> by_cases hjn : j=n
        · exact (hij (hin.trans hjn.symm)).elim
        · obtain ⟨na,nb⟩ := away j hj hjn
          simp [hin,hjn, na, nb]
        · obtain ⟨na,nb⟩ := away i hi hin
          simp [hin,hjn, na, nb]
        · simp [hin,hjn,Ne.symm hij]
    · have na := earlier a (by simp [hargs])
      have nb := earlier b (by simp [hargs])
      ext z
      simp only [Formula.bind_leaves, List.mem_toFinset, List.mem_flatMap]
      rw [live, ite_eq_left used]
      simp only [Finset.mem_union, Finset.mem_erase, Finset.mem_filter, hargs, List.mem_toFinset,
        List.mem_cons, List.not_mem_nil, or_false]
      have hmem (i : ℕ) : i ∈ t.leaves ↔ i ∈ live gs (n+1) o := by
        rw [←support, List.mem_toFinset]
      constructor
      · rintro ⟨i,hi,hz⟩
        by_cases e : i=n
        · subst i; simp [lk] at hz; exact Or.inr ⟨hz, by rcases hz with rfl|rfl <;> assumption⟩
        · simp [lk,e] at hz; subst z; exact Or.inl ⟨e,(hmem _).mp hi⟩
      · rintro (⟨hn,hz⟩|⟨hz,_⟩)
        · exact ⟨z,(hmem _).mpr hz,by simp [lk,hn]⟩
        · exact ⟨n,(hmem _).mpr used,by simpa [lk] using hz⟩
    · intro x hx
      rw [Formula.bind_eval]
      change _ = (Circuit.mk gs o).eval (advance g x)
      rw [←semantics (advance g x) (by simp [advance,hx])]
      congr 1
      funext i
      by_cases eq : i=n
      · subst i
        rw [show (advance g x).getD n false = _ by simpa only [hx] using getD_advance_eq g x]
        have hop : g.op = .and ∨ g.op = .or := (legal g (List.mem_cons_self ..)).1
        rcases hop with e|e <;>
          simp [k, op, e, hargs, Formula.eval, GateOp.eval]
      · by_cases small : i<n
        · simp only [k, if_neg eq, Formula.eval]
          exact (getD_advance_lt g x i (by omega)).symm
        · have big : (advance g x).length ≤ i := by simp [advance,hx]; omega
          simp only [k, if_neg eq, Formula.eval]
          rw [getD_missing big, getD_missing (by omega : x.length ≤ i)]

theorem formula_of_tight_circuit {n m : ℕ} {A : Fin n → Fin m → Bool}
    {C : Circuit} (legal : Monotone2 C) (rep : Represents A C)
    (positive : 0 < charged A) (cost : C.size ≤ charged A - 1) :
    ∃ t : Formula, t.leaves.Nodup ∧ t.leaves.toFinset = live C.gates (n+m) C.output ∧
      ∀ x : List Bool, x.length = n+m →
        t.eval (fun i => x.getD i false) = C.eval x := by
  exact formula_of_sweep C.gates (n+m) C.output legal
    (tight_physical_sweep legal rep positive cost).2.2

end OnePerShore


namespace ReadOnceP4

/-- A possible final gate of a positive read-once formula. Its two
children receive disjoint subsets of the four varying leaves. -/
def rootValue (useAnd a b c d : Bool) (f g : Bool → Bool → Bool → Bool → Bool)
    (x y z w : Bool) : Bool :=
  let l := f (a && x) (b && y) (c && z) (d && w)
  let r := g (!a && x) (!b && y) (!c && z) (!d && w)
  if useAnd then l && r else l || r

/-- A connected three-edge bipartite path, with its missing corner
rejected, cannot have a nontrivial read-once root split. The child
functions may be arbitrary apart from vanishing on the zero vector. -/
theorem no_split (op a b c d : Bool) (f g : Bool → Bool → Bool → Bool → Bool)
    (leftUsed : a || b || c || d = true)
    (rightUsed : !a || !b || !c || !d = true)
    (fzero : f false false false false = false)
    (gzero : g false false false false = false)
    (sx : rootValue op a b c d f g true false false false = false)
    (sy : rootValue op a b c d f g false true false false = false)
    (sz : rootValue op a b c d f g false false true false = false)
    (sw : rootValue op a b c d f g false false false true = false)
    (xz : rootValue op a b c d f g true false true false = true)
    (xw : rootValue op a b c d f g true false false true = true)
    (yz : rootValue op a b c d f g false true true false = true)
    (yw : rootValue op a b c d f g false true false true = false) : False := by
  cases op <;> cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all [rootValue] <;> grind

end ReadOnceP4


namespace OnePerShore

abbrev Four := Bool → Bool → Bool → Bool → Bool

def Corner (f : Four) : Prop :=
  f true false false false = false ∧ f false true false false = false ∧
  f false false true false = false ∧ f false false false true = false ∧
  f true false true false = true ∧ f true false false true = true ∧
  f false true true false = true ∧ f false true false true = false

/-- Closure of the obstruction under a root split, including an empty
projected child. The nonempty case is the finite four-variable lemma. -/
private theorem no_corner_split (op a b c d : Bool) (f g : Four)
    (fz : f false false false false = false) (gz : g false false false false = false)
    (hf : ¬ Corner f) (hg : ¬ Corner g) :
    ¬ Corner (ReadOnceP4.rootValue op a b c d f g) := by
  by_cases hl : a || b || c || d = true
  · by_cases hr : !a || !b || !c || !d = true
    · rintro ⟨sx,sy,sz,sw,xz,xw,yz,yw⟩
      exact ReadOnceP4.no_split op a b c d f g hl hr fz gz sx sy sz sw xz xw yz yw
    · cases a <;> cases b <;> cases c <;> cases d <;> cases op <;>
        simp_all [Corner, ReadOnceP4.rootValue]
  · cases a <;> cases b <;> cases c <;> cases d <;> cases op <;>
      simp_all [Corner, ReadOnceP4.rootValue]

def paint (a b c d : ℕ) (x y z w : Bool) (i : ℕ) : Bool :=
  (decide (i=a) && x) || (decide (i=b) && y) ||
  (decide (i=c) && z) || (decide (i=d) && w)

def Formula.trace (t : Formula) (a b c d : ℕ) : Four :=
  fun x y z w => t.eval (paint a b c d x y z w)

theorem Formula.eval_congr (t : Formula) (x y : ℕ → Bool)
    (h : ∀ i ∈ t.leaves, x i = y i) : t.eval x = t.eval y := by
  induction t with
  | atom i => exact h i (by simp [Formula.leaves])
  | node op l r il ir =>
    simp only [Formula.eval]
    rw [il (fun i hi => h i (by simp [Formula.leaves,hi])),
        ir (fun i hi => h i (by simp [Formula.leaves,hi]))]

theorem Formula.eval_zero (t : Formula) : t.eval (fun _ => false) = false := by
  induction t <;> simp_all [Formula.eval]

private theorem trace_zero (t : Formula) (a b c d : ℕ) :
    t.trace a b c d false false false false = false := by
  change t.eval (paint a b c d false false false false) = false
  rw [t.eval_congr _ (fun _ => false) (fun i _ => by simp [paint])]
  exact t.eval_zero

private theorem trace_mask (t : Formula) (a b c d : ℕ) (p : ℕ → Bool)
    (hp : ∀ i ∈ t.leaves, p i = true) (x y z w : Bool) :
    t.trace a b c d (p a && x) (p b && y) (p c && z) (p d && w) =
    t.trace a b c d x y z w := by
  apply Formula.eval_congr
  intro i hi
  have h := hp i hi
  by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;> by_cases hd : i=d <;>
    simp_all [paint]

theorem Formula.no_corner (t : Formula) (nd : t.leaves.Nodup) (a b c d : ℕ) :
    ¬ Corner (t.trace a b c d) := by
  induction t with
  | atom i =>
    by_cases ha : i=a <;> by_cases hb : i=b <;> by_cases hc : i=c <;> by_cases hd : i=d <;>
      simp [Corner,Formula.trace,Formula.eval,paint,ha,hb,hc,hd]
  | node op l r ihl ihr =>
    obtain ⟨nl,nr,apart⟩ := List.nodup_append'.mp nd
    let p := fun i : ℕ => decide (i ∈ l.leaves)
    have hl : ∀ i ∈ l.leaves, p i = true := fun i hi => by simp [p,hi]
    have hr : ∀ i ∈ r.leaves, !(p i) = true := by
      intro i hi
      have hn : i ∉ l.leaves := fun h => (List.disjoint_left.mp apart) h hi
      simp [p,hn]
    have e : ReadOnceP4.rootValue op (p a) (p b) (p c) (p d)
        (l.trace a b c d) (r.trace a b c d) = (Formula.node op l r).trace a b c d := by
      funext x y z w
      unfold ReadOnceP4.rootValue
      rw [trace_mask l a b c d p hl,
        trace_mask r a b c d (fun i => !(p i)) hr]
      rfl
    rw [←e]
    exact no_corner_split op _ _ _ _ _ _ (trace_zero ..) (trace_zero ..) (ihl nl) (ihr nr)

end OnePerShore


namespace OnePerShore
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents

private def pairFlags (i j k : ℕ) : Bool := decide (k=i) || decide (k=j)

private theorem oneEach_getD {n m : ℕ} (u : Fin n) (v : Fin m) (i : ℕ) :
    (oneEach u v).getD i false = pairFlags u.val (n+v.val) i := by
  by_cases hn : i<n
  · have ne : i ≠ n+v.val := by omega
    have fin : (⟨i,hn⟩ : Fin n) = u ↔ i=u.val := Fin.ext_iff
    simp [pairFlags,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,hn,ne,fin]
  · have ne : i ≠ u.val := by omega
    by_cases hm : i-n<m
    · have fin : (⟨i-n,hm⟩ : Fin m) = v ↔ i=n+v.val := by
        rw [Fin.ext_iff]; change i-n=v.val ↔ _; omega
      simp [pairFlags, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        Nat.le_of_not_gt hn, ne, hm, fin]
    · have ne' : i ≠ n+v.val := by omega
      simp [pairFlags, oneEach, List.getD_eq_getElem?_getD, List.getElem?_append_right,
        Nat.le_of_not_gt hn, ne, hm, ne']

private theorem Formula.eval_mono (t : Formula) (x y : ℕ → Bool)
    (h : ∀ i, x i = true → y i = true) : t.eval x = true → t.eval y = true := by
  induction t with
  | atom i => exact h i
  | node op l r hl hr =>
    cases op <;> simp only [Formula.eval,Bool.false_eq_true,ite_false,ite_true,
      Bool.and_eq_true,Bool.or_eq_true] <;> tauto

/-- A missing corner on nonuniversal vertices raises the physical gate
floor by one. The missing corner itself witnesses two nonuniversal flags. -/
theorem physical_corner_lower {n m s : ℕ} {A : Fin n → Fin m → Bool}
    (u w : Fin n) (v z : Fin m)
    (uv : A u v = true) (uz : A u z = true) (wv : A w v = true) (wz : A w z = false)
    (u_nonuniv : ∃ j, A u j = false) (v_nonuniv : ∃ i, A i v = false)
    (bound : RepSizeAtMost A s) : charged A ≤ s := by
  by_contra h
  obtain ⟨C,legal,size,rep⟩ := bound
  obtain ⟨t,nd,_,sem⟩ := formula_of_tight_circuit legal rep (by omega) (by omega)
  have trep (i : Fin n) (j : Fin m) : t.eval (pairFlags i.val (n+j.val)) = A i j := by
    have he := sem (oneEach i j) (by simp [oneEach])
    simpa only [oneEach_getD, rep i j] using he
  have row (i : Fin n) (j : Fin m) (zero : A i j = false) :
      t.eval (fun k => decide (k=i.val)) = false := by
    cases he : t.eval (fun k => decide (k=i.val)) with
    | false => rfl
    | true =>
      have z := t.eval_mono _ (pairFlags i.val (n+j.val)) (fun k hk => by simp [pairFlags,hk]) he
      simp [trep i j,zero] at z
  have col (i : Fin n) (j : Fin m) (zero : A i j = false) :
      t.eval (fun k => decide (k=n+j.val)) = false := by
    cases he : t.eval (fun k => decide (k=n+j.val)) with
    | false => rfl
    | true =>
      have z := t.eval_mono _ (pairFlags i.val (n+j.val)) (fun k hk => by simp [pairFlags,hk]) he
      simp [trep i j,zero] at z
  obtain ⟨j,hj⟩ := u_nonuniv
  obtain ⟨i,hi⟩ := v_nonuniv
  apply t.no_corner nd u.val w.val (n+v.val) (n+z.val)
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (row u j hj)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (row w z wz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (col i v hi)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans (col w z wz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep u v).trans uv)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep u z).trans uz)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep w v).trans wv)
  · unfold Formula.trace
    exact (t.eval_congr _ _ (fun k _ => by simp [paint,pairFlags])).trans ((trep w z).trans wz)

end OnePerShore


namespace OnePerShore
open PEqualNP.Represents

/-- Retain only positive columns having a rejecting original neighbor. -/
def residualProfile {n m : ℕ} (A : Fin n → Fin m → Bool) (u : Fin n) : Finset (Fin m) :=
  Finset.univ.filter fun v => A u v = true ∧ ∃ i, A i v = false

/-- At the physical floor, any two nonuniversal rows with a common
residual neighbor have identical residual neighborhoods. This algebraic
condition says every nonisolated residual component is a biclique. -/
theorem residual_profiles_at_floor {n m : ℕ} {A : Fin n → Fin m → Bool}
    (rep : RepSizeAtMost A (charged A - 1)) (hk : 0 < charged A)
    (u w : Fin n) (hu : ∃ j, A u j = false) (hw : ∃ j, A w j = false)
    (common : ∃ v, v ∈ residualProfile A u ∧ v ∈ residualProfile A w) :
    residualProfile A u = residualProfile A w := by
  obtain ⟨v,vu,vw⟩ := common
  have vu' := (Finset.mem_filter.mp vu).2
  have vw' := (Finset.mem_filter.mp vw).2
  have incl (r q : Fin n) (neg : ∃ j, A r j = false)
      (rv : A r v = true) (qv : A q v = true) :
      residualProfile A r ⊆ residualProfile A q := by
    intro z hz
    obtain ⟨rz,cz⟩ := (Finset.mem_filter.mp hz).2
    by_cases qz : A q z = true
    · exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,qz,cz⟩
    · have qz' : A q z = false := by simpa using qz
      have h := physical_corner_lower r q v z rv rz qv qz' neg vu'.2 rep
      omega
  exact Finset.Subset.antisymm (incl u w hu vu'.1 vw'.1) (incl w u hw vw'.1 vu'.1)

end OnePerShore


/-! The expression compiler and its simulation proof below are adapted from
PEqualNP/Library/Helpers/TableauExpr.lean (Apache-2.0, open-goat/pequalnp-proofs).
Only the compiler prefix and its semantic contract are needed here. -/
namespace OnePerShore.Upper.Compiler

open PEqualNP.CircuitLowerBounds

/-- Formulas. -/
inductive Ex (α : Type) where
  | var : α → Ex α
  | const : Bool → Ex α
  | not : Ex α → Ex α
  | and : Ex α → Ex α → Ex α
  | or : Ex α → Ex α → Ex α

namespace Ex

variable {α β : Type}

/-- Value of a formula. -/
def eval (ρ : α → Bool) : Ex α → Bool
  | var a => ρ a
  | const b => b
  | not e => !(eval ρ e)
  | and e f => eval ρ e && eval ρ f
  | or e f => eval ρ e || eval ρ f

/-- Number of nodes. -/
def size : Ex α → ℕ
  | var _ => 1
  | const _ => 1
  | not e => size e + 1
  | and e f => size e + size f + 1
  | or e f => size e + size f + 1

/-- Substitution. -/
def bind (σ : α → Ex β) : Ex α → Ex β
  | var a => σ a
  | const b => const b
  | not e => not (bind σ e)
  | and e f => and (bind σ e) (bind σ f)
  | or e f => or (bind σ e) (bind σ f)

theorem eval_bind (ρ : β → Bool) (σ : α → Ex β) (e : Ex α) :
    eval ρ (bind σ e) = eval (fun a => eval ρ (σ a)) e := by
  induction e with
  | var a => rfl
  | const b => rfl
  | not e ih => simp [bind, eval, ih]
  | and e f ih1 ih2 => simp [bind, eval, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, eval, ih1, ih2]

theorem size_bind (σ : α → Ex β) (hσ : ∀ a, size (σ a) = 1) (e : Ex α) :
    size (bind σ e) = size e := by
  induction e with
  | var a => exact hσ a
  | const b => rfl
  | not e ih => simp [bind, size, ih]
  | and e f ih1 ih2 => simp [bind, size, ih1, ih2]
  | or e f ih1 ih2 => simp [bind, size, ih1, ih2]

end Ex

open Ex

/-! ## Wires -/

/-- All wires after running a gate list on the wire list `W`. -/
def run (gs : List Gate) (W : List Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) W

theorem run_wires (C : Circuit) (x : List Bool) : C.wires x = run C.gates x := rfl

theorem run_append (gs gs' : List Gate) (W : List Bool) :
    run (gs ++ gs') W = run gs' (run gs W) := by
  simp [run, List.foldl_append]

theorem run_nil (W : List Bool) : run [] W = W := rfl

theorem run_single (g : Gate) (W : List Bool) :
    run [g] W = W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)] := rfl

theorem run_prefix (gs : List Gate) : ∀ W : List Bool, ∃ t, run gs W = W ++ t := by
  induction gs with
  | nil => intro W; exact ⟨[], by simp [run]⟩
  | cons g gs ih =>
    intro W
    obtain ⟨t, ht⟩ := ih (W ++ [g.op.eval (g.inputs.map fun i => W.getD i false)])
    refine ⟨[g.op.eval (g.inputs.map fun i => W.getD i false)] ++ t, ?_⟩
    change run gs _ = _
    rw [ht, List.append_assoc]

theorem length_run (gs : List Gate) : ∀ W : List Bool, (run gs W).length = W.length + gs.length := by
  induction gs with
  | nil => intro W; simp [run]
  | cons g gs ih =>
    intro W
    change (run gs _).length = _
    rw [ih]; simp; omega

theorem getD_run (gs : List Gate) (W : List Bool) (i : ℕ) (h : i < W.length) :
    (run gs W).getD i false = W.getD i false := by
  obtain ⟨t, ht⟩ := run_prefix gs W
  rw [ht, List.getD_append _ _ _ _ h]

/-- `W` carries `ρ` on the wires `w`. -/
def Rep {α : Type} (W : List Bool) (w : α → ℕ) (ρ : α → Bool) : Prop :=
  ∀ a, w a < W.length ∧ W.getD (w a) false = ρ a

theorem rep_run {α : Type} {W : List Bool} {w : α → ℕ} {ρ : α → Bool} (h : Rep W w ρ)
    (gs : List Gate) : Rep (run gs W) w ρ := by
  intro a
  refine ⟨?_, ?_⟩
  · rw [length_run]; have := (h a).1; omega
  · rw [getD_run _ _ _ (h a).1]; exact (h a).2

/-- A gate allowed in `SIZE`. -/
def Basic (g : Gate) : Prop :=
  g.op ∈ ({GateOp.and, GateOp.or, GateOp.not} : Set GateOp) ∧ g.inputs.length ≤ 2

/-! ## Compiling one formula -/

section compile

variable {α : Type} (w : α → ℕ)

/-- The gates of a formula appended after `N` wires, and its output wire. -/
def compile : Ex α → ℕ → List Gate × ℕ
  | .var a, _ => ([], w a)
  | .const b, N => ([⟨if b then GateOp.and else GateOp.or, []⟩], N)
  | .not e, N =>
    let p := compile e N
    (p.1 ++ [⟨GateOp.not, [p.2]⟩], N + p.1.length)
  | .and e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.and, [p.2, q.2]⟩], N + p.1.length + q.1.length)
  | .or e f, N =>
    let p := compile e N
    let q := compile f (N + p.1.length)
    (p.1 ++ q.1 ++ [⟨GateOp.or, [p.2, q.2]⟩], N + p.1.length + q.1.length)

theorem compile_basic : ∀ (e : Ex α) (N : ℕ), ∀ g ∈ (compile w e N).1, Basic g
  | .var a, N => by simp [compile]
  | .const b, N => by
    intro g hg
    simp only [compile, List.mem_singleton] at hg
    subst hg
    cases b <;> simp [Basic]
  | .not e, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with hg | hg
    · exact compile_basic e N g hg
    · subst hg; simp [Basic]
  | .and e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]
  | .or e f, N => by
    intro g hg
    simp only [compile, List.mem_append, List.mem_singleton] at hg
    rcases hg with (hg | hg) | hg
    · exact compile_basic e N g hg
    · exact compile_basic f _ g hg
    · subst hg; simp [Basic]

theorem compile_length : ∀ (e : Ex α) (N : ℕ), (compile w e N).1.length ≤ size e
  | .var a, N => by simp [compile, size]
  | .const b, N => by simp [compile, size]
  | .not e, N => by
    have := compile_length e N
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .and e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega
  | .or e f, N => by
    have := compile_length e N
    have := compile_length f (N + (compile w e N).1.length)
    simp only [compile, size, List.length_append, List.length_singleton]; omega

theorem getD_snoc_len (W : List Bool) (b : Bool) : (W ++ [b]).getD W.length false = b := by
  simp

theorem compile_spec : ∀ (e : Ex α) (W : List Bool) (ρ : α → Bool), Rep W w ρ →
    (compile w e W.length).2 < W.length + (compile w e W.length).1.length ∧
    (run (compile w e W.length).1 W).getD (compile w e W.length).2 false = eval ρ e
  | .var a, W, ρ, h => by
    simp only [compile, List.length_nil, Nat.add_zero, run_nil, eval]
    exact h a
  | .const b, W, ρ, h => by
    simp only [compile, List.length_singleton, run_single, eval]
    refine ⟨by omega, ?_⟩
    rw [getD_snoc_len]
    cases b <;> simp [GateOp.eval]
  | .not e, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    have hl := length_run (compile w e W.length).1 W
    rw [← hl, getD_snoc_len]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.headD_cons]
    exact congrArg _ h2
  | .and e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.all_cons, List.all_nil, id,
      Bool.and_true]
    exact congrArg₂ _ e2 h4
  | .or e f, W, ρ, h => by
    obtain ⟨h1, h2⟩ := compile_spec e W ρ h
    set p := compile w e W.length
    have hl := length_run p.1 W
    have h' := rep_run h p.1
    obtain ⟨h3, h4⟩ := compile_spec f (run p.1 W) ρ h'
    rw [hl] at h3 h4
    simp only [compile, List.length_append, List.length_singleton, run_append, run_single,
      eval]
    refine ⟨by omega, ?_⟩
    set q := compile w f (W.length + p.1.length)
    have hl2 := length_run q.1 (run p.1 W)
    rw [hl] at hl2
    have e1 : W.length + p.1.length + q.1.length = (run q.1 (run p.1 W)).length := by
      rw [hl2]
    rw [e1, getD_snoc_len]
    have e2 : (run q.1 (run p.1 W)).getD p.2 false = eval ρ e := by
      rw [getD_run _ _ _ (by rw [hl]; omega), h2]
    simp only [GateOp.eval, List.map_cons, List.map_nil, List.any_cons, List.any_nil, id,
      Bool.or_false]
    exact congrArg₂ _ e2 h4

end compile
end OnePerShore.Upper.Compiler


namespace OnePerShore.Upper

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents
open Compiler

/-- Number of leaves in a nonempty monotone binary expression. -/
inductive Leaves {α : Type} : Ex α → ℕ → Prop where
  | var (a : α) : Leaves (.var a) 1
  | and {e f : Ex α} {i j} : Leaves e i → Leaves f j → Leaves (.and e f) (i+j)
  | or {e f : Ex α} {i j} : Leaves e i → Leaves f j → Leaves (.or e f) (i+j)

theorem Leaves.cost {α} {e : Ex α} {k} (h : Leaves e k) (w : α → ℕ) (N : ℕ) :
    (compile w e N).1.length + 1 = k := by
  induction h generalizing N with
  | var => simp [compile]
  | @and e f i j _ _ a b | @or e f i j _ _ a b =>
    simp only [compile,List.length_append,List.length_singleton]
    have l := a N
    have r := b (N + (compile w e N).1.length)
    omega

theorem Leaves.legal {α} {e : Ex α} {k} (h : Leaves e k) (w : α → ℕ) (N : ℕ) :
    ∀ g ∈ (compile w e N).1, g.op ∈ ({GateOp.and,GateOp.or} : Set GateOp) ∧ g.inputs.length ≤ 2 := by
  induction h generalizing N with
  | var => simp [compile]
  | and _ _ a b | or _ _ a b =>
    intro g hg
    simp only [compile,List.mem_append,List.mem_singleton] at hg
    rcases hg with (h | h) | h
    · exact a _ g h
    · exact b _ g h
    · subst g; simp

abbrev Pred (n m : ℕ) := Fin n → Fin m → Bool
def readFlag {n m} (u : Fin n) (v : Fin m) : Fin n ⊕ Fin m → Bool
  | .inl i => decide (i=u)
  | .inr j => decide (j=v)

def Built {n m} (A : Pred n m) (k : ℕ) : Prop :=
  ∃ e : Ex (Fin n ⊕ Fin m), Leaves e k ∧ ∀ u v, e.eval (readFlag u v) = A u v

theorem Built.realize {n m k} {A : Pred n m} (b : Built A k) :
    RepSizeAtMost A (k-1) := by
  obtain ⟨e,h,sem⟩ := b
  let w : Fin n ⊕ Fin m → ℕ := Sum.elim Fin.val (fun j => n + j.val)
  let p := compile w e (n+m)
  refine ⟨⟨p.1,p.2⟩,h.legal w (n+m),?_,?_⟩
  · change (compile w e (n+m)).1.length ≤ k-1
    have := h.cost w (n+m); omega
  · intro u v
    have he : Rep (oneEach u v) w (readFlag u v) := by
      intro a
      cases a with
      | inl i =>
        simp [w,readFlag,oneEach,List.getD_eq_getElem?_getD,List.getElem?_append_left,i.isLt]
        omega
      | inr j =>
        simp [w,readFlag,oneEach,List.getD_eq_getElem?_getD]
    have hv := (compile_spec w e (oneEach u v) _ he).2
    rw [show (oneEach u v).length = n+m by simp [oneEach]] at hv
    exact hv.trans (sem u v)

theorem Built.and {n m a b} {A B : Pred n m} (ha : Built A a) (hb : Built B b) :
    Built (fun u v => A u v && B u v) (a+b) := by
  obtain ⟨e,h,s⟩ := ha; obtain ⟨f,h',s'⟩ := hb
  exact ⟨.and e f,.and h h',fun u v => by simp [Ex.eval,s,s']⟩

theorem Built.or {n m a b} {A B : Pred n m} (ha : Built A a) (hb : Built B b) :
    Built (fun u v => A u v || B u v) (a+b) := by
  obtain ⟨e,h,s⟩ := ha; obtain ⟨f,h',s'⟩ := hb
  exact ⟨.or e f,.or h h',fun u v => by simp [Ex.eval,s,s']⟩

open scoped BigOperators
noncomputable def anyOn {n m} {ι : Type} (s : Finset ι) (f : ι → Pred n m) : Pred n m := by
  classical
  exact fun u v => decide (∃ i ∈ s,f i u v = true)

theorem built_any {n m} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Pred n m) (k : ι → ℕ) :
    s.Nonempty → (∀ i ∈ s, Built (f i) (k i)) →
    Built (anyOn s f) (∑ i ∈ s,k i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s fresh ih =>
    intro _ h
    have ha := h a (Finset.mem_insert_self ..)
    by_cases hs : s.Nonempty
    · have htail := ih hs (fun x hx => h _ (Finset.mem_insert_of_mem hx))
      have eq : anyOn (insert a s) f = (fun u v => f a u v || anyOn s f u v) := by
        funext u v; apply Bool.eq_iff_iff.mpr; simp [anyOn]
      simpa [eq,Finset.sum_insert,fresh] using ha.or htail
    · have := Finset.not_nonempty_iff_eq_empty.mp hs
      subst s
      have eq : anyOn {a} f = f a := by
        funext u v; apply Bool.eq_iff_iff.mpr; simp [anyOn]
      simpa [eq] using ha

end OnePerShore.Upper


namespace OnePerShore.Upper
open PEqualNP.Represents
open scoped BigOperators

theorem rowBuilt {n m} (i : Fin n) : Built (fun (u : Fin n) (_ : Fin m) => decide (u=i)) 1 :=
  ⟨.var (.inl i),.var _,fun u v => by simp [Compiler.Ex.eval,readFlag,eq_comm]⟩

theorem colBuilt {n m} (j : Fin m) : Built (fun (_ : Fin n) (v : Fin m) => decide (v=j)) 1 :=
  ⟨.var (.inr j),.var _,fun u v => by simp [Compiler.Ex.eval,readFlag,eq_comm]⟩

theorem rectBuilt {n m} (r : Finset (Fin n)) (c : Finset (Fin m)) (hr : r.Nonempty) (hc : c.Nonempty) :
    Built (fun u v => decide (u ∈ r ∧ v ∈ c)) (r.card+c.card) := by
  have a := built_any r (fun i (u : Fin n) (_ : Fin m) => decide (u=i)) (fun _ => 1)
    hr (fun i _ => rowBuilt i)
  have b := built_any c (fun j (_ : Fin n) (v : Fin m) => decide (v=j)) (fun _ => 1)
    hc (fun j _ => colBuilt j)
  simpa [anyOn] using a.and b

inductive Term (n m : ℕ) where
  | row (i : Fin n)
  | col (j : Fin m)
  | box (r : Finset (Fin n)) (c : Finset (Fin m))
deriving DecidableEq

def Term.weight {n m} : Term n m → ℕ
  | .row _ | .col _ => 1
  | .box r c => r.card+c.card

def Term.valid {n m} : Term n m → Prop
  | .row _ | .col _ => True
  | .box r c => r.Nonempty ∧ c.Nonempty

def Term.pred {n m} : Term n m → Pred n m
  | .row i => fun u _ => decide (u=i)
  | .col j => fun _ v => decide (v=j)
  | .box r c => fun u v => decide (u ∈ r ∧ v ∈ c)

theorem Term.built {n m} (t : Term n m) (h : t.valid) : Built t.pred t.weight := by
  cases t with
  | row i => exact rowBuilt i
  | col j => exact colBuilt j
  | box r c => exact rectBuilt r c h.1 h.2

theorem physical_of_partition {n m} (A : Pred n m) (terms : Finset (Term n m))
    (ne : terms.Nonempty) (valid : ∀ t ∈ terms,t.valid)
    (rep : ∀ u v, A u v = true ↔ ∃ t ∈ terms,t.pred u v = true)
    (count : ∑ t ∈ terms,t.weight = charged A) :
    RepSizeAtMost A (charged A - 1) := by
  have b := built_any terms Term.pred Term.weight ne (fun t ht => t.built (valid t ht))
  have eq : anyOn terms Term.pred = A := by
    funext u v; apply Bool.eq_iff_iff.mpr; simpa [anyOn] using (rep u v).symm
  rw [eq,count] at b
  exact b.realize

end OnePerShore.Upper


namespace OnePerShore.Upper
open PEqualNP.Represents
open scoped BigOperators

/-- Nonuniversal row profiles are either disjoint or equal. -/
def BicliqueResidual {n m} (A : Pred n m) : Prop :=
  ∀ u w, (∃ j, A u j = false) → (∃ j,A w j = false) →
    (∃ j, j ∈ residualProfile A u ∧ j ∈ residualProfile A w) →
      residualProfile A u = residualProfile A w

def uRows {n m} (A : Pred n m) : Finset (Fin n) :=
  Finset.univ.filter fun i => ∀ j,A i j = true
def uCols {n m} (A : Pred n m) : Finset (Fin m) :=
  Finset.univ.filter fun j => ∀ i,A i j = true
def activeRows {n m} (A : Pred n m) : Finset (Fin n) :=
  (nonminimumRows A) \ (uRows A)
def profiles {n m} (A : Pred n m) := (activeRows A).image (residualProfile A)
def owners {n m} (A : Pred n m) (c : Finset (Fin m)) :=
  (activeRows A).filter fun i => residualProfile A i = c

private theorem active_profile {n m} {A : Pred n m} {i} (h : i ∈ activeRows A) :
    (residualProfile A i).Nonempty := by
  obtain ⟨j,w,p,z⟩ := (Finset.mem_filter.mp (Finset.mem_sdiff.mp h).1).2
  exact ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,z⟩⟩

private theorem profile_origin {n m} {A : Pred n m} {c} (h : c ∈ profiles A) :
    ∃ i ∈ activeRows A, residualProfile A i = c := Finset.mem_image.mp h

private theorem active_cold {n m} {A : Pred n m} {u} (hu : u ∈ activeRows A) :
    ∃ j,A u j = false := by
  have h := (Finset.mem_sdiff.mp hu).2
  simpa [uRows] using h

private theorem classes_disjoint {n m} {A : Pred n m} (clean : BicliqueResidual A) :
    (↑(profiles A) : Set (Finset (Fin m))).PairwiseDisjoint id := by
  intro c hc d hd ne
  obtain ⟨i,hi,rfl⟩ := profile_origin hc
  obtain ⟨j,hj,rfl⟩ := profile_origin hd
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact ne (clean i j (active_cold hi) (active_cold hj) ⟨v,hv,hw⟩)

private theorem row_card {n m} {A : Pred n m} (zero : ∃ i j,A i j=false) :
    (uRows A).card + (activeRows A).card = (nonminimumRows A).card := by
  obtain ⟨i,j,h⟩ := zero
  have sub : uRows A ⊆ nonminimumRows A := by
    intro u hu
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,i,(Finset.mem_filter.mp hu).2 j,h⟩
  simpa [activeRows,Nat.add_comm] using Finset.card_sdiff_add_card_eq_card sub

private theorem col_card {n m} {A : Pred n m} (zero : ∃ i j,A i j=false) :
    (uCols A).card + ((profiles A).biUnion id).card = (nonminimumCols A).card := by
  classical
  obtain ⟨r,z,rz⟩ := zero
  have eq : (profiles A).biUnion id = (nonminimumCols A) \ (uCols A) := by
    ext j
    constructor
    · intro h
      obtain ⟨c,hc,hj⟩ := Finset.mem_biUnion.mp h
      obtain ⟨i,hi,rfl⟩ := profile_origin hc
      obtain ⟨pos,w,neg⟩ := (Finset.mem_filter.mp hj).2
      obtain ⟨v,hv⟩ := active_cold hi
      exact Finset.mem_sdiff.mpr ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,i,v,pos,hv⟩,
        fun hu => by simpa [neg] using (Finset.mem_filter.mp hu).2 w⟩
    · intro h
      obtain ⟨ic,nc⟩ := Finset.mem_sdiff.mp h
      obtain ⟨i,v,p,q⟩ := (Finset.mem_filter.mp ic).2
      have ex : ∃ w,A w j=false := by simpa [uCols] using nc
      obtain ⟨w,hw⟩ := ex
      have ia : i ∈ activeRows A := Finset.mem_sdiff.mpr
        ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,j,w,p,hw⟩,
          fun hu => by simpa [q] using (Finset.mem_filter.mp hu).2 v⟩
      exact Finset.mem_biUnion.mpr ⟨_,Finset.mem_image_of_mem _ ia,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,hw⟩⟩
  rw [eq]
  have sub : uCols A ⊆ nonminimumCols A := by
    intro j hj
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,r,z,(Finset.mem_filter.mp hj).2 r,rz⟩
  simpa [Nat.add_comm] using Finset.card_sdiff_add_card_eq_card sub

private def PartialBuilt {n m} (A : Pred n m) (k : ℕ) : Prop :=
  (k=0 ∧ A=fun _ _ => false) ∨ Built A k

private theorem partial_or {n m a b} {A B : Pred n m} (ha : PartialBuilt A a)
    (hb : PartialBuilt B b) : PartialBuilt (fun u v => A u v || B u v) (a+b) := by
  rcases ha with ⟨rfl,rfl⟩ | ha
  · simpa using hb
  rcases hb with ⟨rfl,rfl⟩ | hb
  · apply Or.inr; simpa using ha
  exact Or.inr (ha.or hb)

private theorem partial_any {n m} {ι : Type} [DecidableEq ι] (s : Finset ι)
    (f : ι → Pred n m) (k : ι → ℕ) (h : ∀ i∈s,Built (f i) (k i)) :
    PartialBuilt (anyOn s f) (∑ i∈s,k i) := by
  classical
  by_cases hs : s.Nonempty
  · exact Or.inr (built_any s f k hs h)
  · have := Finset.not_nonempty_iff_eq_empty.mp hs
    subst s
    exact Or.inl ⟨by simp,by funext u v; simp [anyOn]⟩

private def boxPred {n m} (A : Pred n m) (c : Finset (Fin m)) : Pred n m :=
  fun u v => decide (u ∈ owners A c ∧ v∈c)

private theorem cover_spec {n m} (A : Pred n m) (u : Fin n) (v : Fin m) :
    A u v=true ↔ u∈uRows A ∨ v∈uCols A ∨ ∃ c∈profiles A,u∈owners A c ∧ v∈c := by
  constructor
  · intro p
    by_cases hr : u∈uRows A
    · exact Or.inl hr
    by_cases hc : v∈uCols A
    · exact Or.inr (Or.inl hc)
    have ex : ∃ w,A w v=false := by simpa [uCols] using hc
    obtain ⟨w,hw⟩ := ex
    have ia : u∈activeRows A := Finset.mem_sdiff.mpr
      ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,w,p,hw⟩,hr⟩
    exact Or.inr (Or.inr ⟨_,Finset.mem_image_of_mem _ ia,Finset.mem_filter.mpr ⟨ia,rfl⟩,
      Finset.mem_filter.mpr ⟨Finset.mem_univ _,p,w,hw⟩⟩)
  · rintro (hu | hv | ⟨c,_,hu,hv⟩)
    · exact (Finset.mem_filter.mp hu).2 v
    · exact (Finset.mem_filter.mp hv).2 u
    · have e : residualProfile A u=c := (Finset.mem_filter.mp hu).2
      rw [←e] at hv
      exact (Finset.mem_filter.mp hv).2.1

theorem physical_of_biclique_residual {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) (clean : BicliqueResidual A) :
    RepSizeAtMost A (charged A - 1) := by
  classical
  let r : Fin n → Pred n m := fun i u _ => decide (u=i)
  let c : Fin m → Pred n m := fun j _ v => decide (v=j)
  let w := fun s : Finset (Fin m) => (owners A s).card+s.card
  have ar := partial_any (uRows A) r (fun _ => 1) (fun i _ => rowBuilt i)
  have ac := partial_any (uCols A) c (fun _ => 1) (fun j _ => colBuilt j)
  have ab := partial_any (profiles A) (boxPred A) w (by
    intro s hs
    obtain ⟨i,hi,rfl⟩ := profile_origin hs
    exact rectBuilt _ _ ⟨i,Finset.mem_filter.mpr ⟨hi,rfl⟩⟩ (active_profile hi))
  have whole := partial_or ar (partial_or ac ab)
  have eq : (fun u v => anyOn (uRows A) r u v ||
      (anyOn (uCols A) c u v || anyOn (profiles A) (boxPred A) u v)) = A := by
    funext u v; apply Bool.eq_iff_iff.mpr
    simpa [anyOn,r,c,boxPred] using (cover_spec A u v).symm
  have fiber : (∑ s ∈ profiles A, (owners A s).card) = (activeRows A).card := by
    unfold owners
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    exact Finset.filter_true_of_mem (fun i hi => Finset.mem_image_of_mem _ hi)
  have cols := Finset.card_biUnion (classes_disjoint clean)
  have cost : (∑ _ ∈ uRows A, 1) + ((∑ _ ∈ uCols A, 1) + ∑ s ∈ profiles A,w s) = charged A := by
    simp only [w,Finset.sum_add_distrib,Finset.sum_const,Nat.nsmul_eq_mul,mul_one,fiber]
    change (uRows A).card + ((uCols A).card + ((activeRows A).card + ∑ s ∈ profiles A,s.card)) =
      (nonminimumRows A).card + (nonminimumCols A).card
    change ((profiles A).biUnion id).card = ∑ s ∈ profiles A,s.card at cols
    have := row_card zero; have := col_card zero; omega
  rw [eq,cost] at whole
  rcases whole with ⟨_,eq⟩ | b
  · obtain ⟨u,v,h⟩ := pos
    simp [eq] at h
  · exact b.realize

theorem exact_floor_iff {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) :
    RepSizeAtMost A (charged A - 1) ↔ BicliqueResidual A := by
  constructor
  · intro h
    by_cases hp : 0 < charged A
    · exact residual_profiles_at_floor h hp
    · intro u w hu hw hv
      obtain ⟨v,hv,_⟩ := hv
      obtain ⟨p,i,neg⟩ := (Finset.mem_filter.mp hv).2
      have row : u ∈ nonminimumRows A := Finset.mem_filter.mpr ⟨Finset.mem_univ _,v,i,p,neg⟩
      have := Finset.card_pos.mpr ⟨_,row⟩
      unfold charged at hp
      omega
  · exact physical_of_biclique_residual A pos zero

/-- The constructed upper bound attains the exact gate count, including zero. -/
theorem exact_circuit_of_biclique_residual {n m} (A : Pred n m)
    (pos : ∃ u v,A u v=true) (zero : ∃ u v,A u v=false) (clean : BicliqueResidual A) :
    ∃ C : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.MetaComplexity.Monotone2 C ∧
      C.size = charged A - 1 ∧ Represents A C := by
  obtain ⟨C,legal,size,rep⟩ := physical_of_biclique_residual A pos zero clean
  have low := physical_size_floor (A:=A) (s:=C.size) ⟨C,legal,le_rfl,rep⟩
  exact ⟨C,legal,Nat.le_antisymm size low,rep⟩

end OnePerShore.Upper


namespace OnePerShore.Upper.Examples
open PEqualNP.Represents

/-- Universal row and two disjoint residual bicliques. -/
def mixed (u : Fin 4) (v : Fin 4) := (49983 : ℕ).testBit (4*u.val+v.val)

/-- The representation has a raw output and uses zero gates. -/
def raw (u : Fin 2) (_ : Fin 2) := decide (u=0)

example : RepSizeAtMost raw 0 := by
  have h := physical_of_biclique_residual raw ⟨0,0,by decide⟩ ⟨1,1,by decide⟩ (by
    unfold BicliqueResidual; decide +kernel)
  exact h

example : RepSizeAtMost mixed 7 := by
  have h := physical_of_biclique_residual mixed ⟨0,0,by decide⟩ ⟨1,3,by decide⟩ (by
    unfold BicliqueResidual; decide +kernel)
  exact h

end OnePerShore.Upper.Examples

#print axioms OnePerShore.Upper.exact_floor_iff
#print axioms OnePerShore.Upper.physical_of_biclique_residual
