import Research.CrownCollisionLimit

namespace PEqualNP.Research.MissingCell
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents CrownDiagonalCharge

def mixedNow (g : Gate) (x r c : List Bool) : Prop :=
  gateBool g x = true ∧ gateBool g r = false ∧ gateBool g c = false

def firstMixed : List Gate → List Bool → List Bool → List Bool → ℕ → Prop
  | [], _, _, _, _ => False
  | g::_, x, r, c, 0 => mixedNow g x r c
  | g::gs, x, r, c, k+1 => ¬mixedNow g x r c ∧
      firstMixed gs (advance g x) (advance g r) (advance g c) k

def pairOpposes (r c : List Bool) (a b : ℕ) : Prop :=
  (r.getD a false = true ∧ c.getD a false = false ∧
    r.getD b false = false ∧ c.getD b false = true) ∨
  (r.getD b false = true ∧ c.getD b false = false ∧
    r.getD a false = false ∧ c.getD a false = true)

private theorem opposite_bits : ∀ x y u v : Bool,
    (x=true ∨ y=true) → (u=true ∨ v=true) →
    (x && u)=false → (y && v)=false →
    (x=true ∧ y=false ∧ u=false ∧ v=true) ∨ (u=true ∧ v=false ∧ x=false ∧ y=true) := by decide

private theorem mixed_parents (g : Gate) (x r c : List Bool)
    (inv : ∀ i, x.getD i false = true → r.getD i false = true ∨ c.getD i false = true)
    (op : g.op = .and ∨ g.op = .or) (len : g.inputs.length ≤ 2)
    (h : mixedNow g x r c) :
    g.op = .and ∧ ∃ a b, g.inputs = [a,b] ∧
      a < x.length ∧ b < x.length ∧ pairOpposes r c a b := by
  obtain ⟨hx,hr,hc⟩ := h
  rcases op with hp|hp
  · refine ⟨hp,?_⟩
    rcases hi : g.inputs with _|⟨a,tl⟩
    · simp [gateBool,hp,hi,GateOp.eval] at hr
    rcases tl with _|⟨b,tl⟩
    · simp only [gateBool,hp,hi,List.map_cons,List.map_nil,GateOp.eval,List.all_cons,List.all_nil,
        Bool.and_true,id_eq] at hx hr hc
      rcases inv a hx with H|H <;> simp_all
    rcases tl with _|⟨d,tl⟩
    · have ax : x.getD a false = true ∧ x.getD b false = true := by
        simpa [gateBool,hp,hi,GateOp.eval,-List.getD_eq_getElem?_getD] using hx
      have lt (p) (t : x.getD p false = true) : p < x.length := by
        by_contra! hh
        rw [getD_missing hh] at t
        contradiction
      refine ⟨a,b,rfl,lt a ax.1,lt b ax.2,?_⟩
      apply opposite_bits _ _ _ _ (inv a ax.1) (inv b ax.2)
      · simpa [gateBool,hp,hi,GateOp.eval] using hr
      · simpa [gateBool,hp,hi,GateOp.eval] using hc
    · simp [hi] at len
  · have someX : ∃ i ∈ g.inputs, x.getD i false = true := by simpa [gateBool,hp,GateOp.eval] using hx
    have noneR : ∀ i ∈ g.inputs, r.getD i false = false := by simpa [gateBool,hp,GateOp.eval] using hr
    have noneC : ∀ i ∈ g.inputs, c.getD i false = false := by simpa [gateBool,hp,GateOp.eval] using hc
    obtain ⟨a,ha,hx⟩ := someX
    rcases inv a hx with H|H
    · rw [noneR a ha] at H
      contradiction
    · rw [noneC a ha] at H
      contradiction

private theorem keep_parent (gs : List Gate) (w : List Bool) (a : ℕ) (ha : a < w.length) :
    ((Circuit.mk gs 0).wires w).getD a false = w.getD a false := by
  induction gs generalizing w with
  | nil => rfl
  | cons g gs ih =>
    change ((Circuit.mk gs 0).wires (advance g w)).getD a false = _
    rw [ih _ (by rw [advance_len];omega),getD_advance_lt _ _ _ ha]

theorem first_mixed_and (C : Circuit) (x r c : List Bool) (hm : Monotone2 C)
    (lr : r.length = x.length) (lc : c.length = x.length)
    (inv : ∀ j, x.getD j false = true → r.getD j false = true ∨ c.getD j false = true)
    (xy : C.eval x = true) (rr : C.eval r = false) (cc : C.eval c = false) :
    ∃ k : Fin C.gates.length, firstMixed C.gates x r c k.val ∧
      ∃ a b, C.gates[k].op = .and ∧ C.gates[k].inputs = [a,b] ∧
        a < x.length+k.val ∧ b < x.length+k.val ∧ pairOpposes (C.wires r) (C.wires c) a b := by
  obtain ⟨gs,out⟩ := C
  induction gs generalizing x r c with
  | nil =>
    rcases inv out xy with H|H
    · change r.getD out false = false at rr
      rw [rr] at H
      contradiction
    · change c.getD out false = false at cc
      rw [cc] at H
      contradiction
  | cons g gs ih =>
    by_cases h : mixedNow g x r c
    · obtain ⟨op,a,b,inputs,al,bl,opposes⟩ :=
        mixed_parents g x r c inv (hm g (by simp)).1 (hm g (by simp)).2 h
      refine ⟨0,h,a,b,op,inputs,al,bl,?_⟩
      change pairOpposes ((Circuit.mk (g::gs) 0).wires r) ((Circuit.mk (g::gs) 0).wires c) a b
      simpa only [pairOpposes,keep_parent (g::gs) r a (by omega), keep_parent (g::gs) r b (by omega),
        keep_parent (g::gs) c a (by omega),keep_parent (g::gs) c b (by omega)] using opposes
    · have next (j : ℕ) (hj : (advance g x).getD j false = true) :
          (advance g r).getD j false = true ∨ (advance g c).getD j false = true := by
        by_cases lt : j < x.length
        · rw [getD_advance_lt _ _ _ lt] at hj
          simpa only [getD_advance_lt g r j (by omega),getD_advance_lt g c j (by omega)] using inv j hj
        by_cases eq : j = x.length
        · subst j
          rw [getD_advance_eq] at hj
          have hr := getD_advance_eq g r
          have hc := getD_advance_eq g c
          rw [lr] at hr
          rw [lc] at hc
          rw [hr,hc]
          change gateBool g x = true at hj
          change gateBool g r = true ∨ gateBool g c = true
          cases R : gateBool g r <;> cases L : gateBool g c <;> simp_all [mixedNow]
        · rw [getD_missing (by rw [advance_len];omega : (advance g x).length ≤ j)] at hj
          contradiction
      obtain ⟨k,hk,a,b,hop,hinputs,ha,hb,opp⟩ := ih (advance g x) (advance g r) (advance g c)
        (by simp [advance_len,lr]) (by simp [advance_len,lc]) next
        (fun z hz => hm z (List.mem_cons_of_mem _ hz)) xy rr cc
      refine ⟨k.succ,⟨h,hk⟩,a,b,hop,hinputs,?_,?_,opp⟩
      · rw [advance_len] at ha
        change a < x.length + (k.val+1)
        omega
      · rw [advance_len] at hb
        change b < x.length + (k.val+1)
        omega

end PEqualNP.Research.MissingCell
