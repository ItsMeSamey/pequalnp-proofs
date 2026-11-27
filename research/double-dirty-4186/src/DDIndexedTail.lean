import Q1DoubleSplit

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double

open PEqualNP.Outside.L_meta_4186_aux.Q0 PEqualNP.Outside.L_meta_4186_aux.Q0.Factor
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.TopForm PEqualNP.CleanedNonEdge

private theorem extendOrPref {n : ℕ} (tail : List (Signal n)) (p : Pack n) (head : p.Wire)
    (rest : ∀ f ∈ tail, Available p f) :
    ∃ (q : Pack n) (out : q.Wire) (keep : p.Wire → q.Wire),
      (∃ suffix, q.gates = p.gates ++ suffix) ∧
      q.gates.length = p.gates.length + tail.length ∧
      (∀ w, (keep w).val = w.val) ∧
      (∀ w x, q.val (keep w) x = p.val w x) ∧
      (∀ x, q.val out x = tail.foldl (join false) (p.val head) x) := by
  induction tail generalizing p with
  | nil => exact ⟨p, head, id, ⟨[], by simp⟩, rfl, fun _ => rfl, fun _ _ => rfl, fun _ => rfl⟩
  | cons f fs ih =>
    obtain ⟨a,ha⟩ := rest f (by simp)
    let r := p.emit false head a
    let newest := p.last false head a
    have hnew : r.val newest = join false (p.val head) f := by
      funext x
      simpa [r, newest, join, ha] using p.val_last false head a x
    have hav (z) (hz : z ∈ fs) : Available r z := by
      obtain ⟨w,hw⟩ := rest z (by simp [hz])
      exact ⟨p.lift false head a w, fun x => (p.val_lift false head a w x).trans (hw x)⟩
    obtain ⟨q,out,keep,⟨suffix,hprefix⟩,hsize,indices,values,result⟩ := ih r newest hav
    refine ⟨q,out,fun w => keep (p.lift false head a w), ?_, ?_, ?_, ?_, ?_⟩
    · rw [hprefix]
      change ∃ t, (p.gates ++ [_]) ++ suffix = p.gates ++ t
      exact ⟨_,List.append_assoc ..⟩
    · simp only [r,Pack.length_emit] at hsize
      simp only [List.length_cons]; omega
    · intro w; exact indices _
    · intro w x; exact (values _ x).trans (p.val_lift false head a w x)
    · intro x; simpa only [List.foldl_cons,hnew] using result x

theorem split_pack {n : ℕ} (p : Pack n)
    (a b w : Signal n) (other : List (Signal n))
    (aw bw ww : p.Wire) (hA : ∀ x, p.val aw x = a x) (hB : ∀ x, p.val bw x = b x)
    (hW : ∀ x, p.val ww x = w x) (ho : ∀ f ∈ other, Available p f) :
    ∃ D : Circuit, IsAO2 n D ∧ (∃ suffix, D.gates = p.gates ++ (⟨.and,[aw.val,ww.val]⟩ :: ⟨.and,[bw.val,ww.val]⟩ :: suffix)) ∧ D.size = p.gates.length + 3 + other.length ∧
      wireVal n D (n+p.gates.length) = join true a w ∧
      wireVal n D (n+(p.gates.length+1)) = join true b w ∧
      circuitFun n D = other.foldl (join false) (join true (join false a b) w) := by
  let p1 := p.emit true aw ww
  let P := p.last true aw ww
  let b1 := p.lift true aw ww bw
  let w1 := p.lift true aw ww ww
  let p2 := p1.emit true b1 w1
  let Q := p1.last true b1 w1
  let P2 := p1.lift true b1 w1 P
  let p3 := p2.emit false P2 Q
  let H := p2.last false P2 Q
  let P3 := p2.lift false P2 Q P2
  let Q3 := p2.lift false P2 Q Q
  have pval (x) : p3.val P3 x = join true a w x := by
    simp [p3,P3,P2,P,p2,p1,join,hA,hW]
  have qval (x) : p3.val Q3 x = join true b w x := by
    simp [p3,Q3,Q,p2,p1,b1,w1,join,hB,hW]
  have hval : p3.val H = join true (join false a b) w := by
    rw [← split_identity a b w]
    funext x
    have hp := pval x
    have hq := qval x
    simp only [p3,P3,Q3,Pack.val_lift] at hp hq
    change (p2.emit false P2 Q).val (p2.last false P2 Q) x = _
    rw [Pack.val_last]
    change (p2.val P2 x || p2.val Q x) = _
    rw [hp,hq] <;> rfl
  have avail (f) (h : f ∈ other) : Available p3 f := by
    obtain ⟨v,hv⟩ := ho f h
    refine ⟨p2.lift false P2 Q (p1.lift true b1 w1 (p.lift true aw ww v)), ?_⟩
    intro x; simp [p3,p2,p1,hv]
  obtain ⟨q,out,keep,⟨suffix,pre⟩,size,indices,values,result⟩ := extendOrPref other p3 H avail
  have hP : (keep P3).val = n+p.gates.length := indices P3
  have hQ : (keep Q3).val = n+(p.gates.length+1) := (indices Q3).trans (by
    change n + (p.emit true aw ww).gates.length = _; rw [Pack.length_emit])
  refine ⟨q.finish out,q.finish_ao2 out,?_,?_,?_,?_,?_⟩
  · change ∃ t, q.gates = p.gates ++ (⟨.and,[aw.val,ww.val]⟩ :: ⟨.and,[bw.val,ww.val]⟩ :: t)
    rw [pre]
    change ∃ t, (((p.gates ++ [⟨.and,[aw.val,ww.val]⟩]) ++ [⟨.and,[bw.val,ww.val]⟩]) ++ [_]) ++ suffix = _
    simp only [List.append_assoc,List.cons_append,List.nil_append]
    exact ⟨_,rfl⟩
  · rw [Pack.finish_size,size]
    simp [p3,p2,p1,Nat.add_assoc]
  · funext x
    rw [← hP]
    exact (values P3 x).trans (pval x)
  · funext x
    rw [← hQ]
    exact (values Q3 x).trans (qval x)
  · funext x
    rw [q.finish_fun out x]
    simpa only [hval] using result x


end PEqualNP.Outside.L_meta_4186_aux.Q1Double
