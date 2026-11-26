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
