import DDIndexedPack
import DDIndexedSem
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm
open PEqualNP.Outside.L_meta_4186_aux
open Q0 Q1Double S4183.S98
def capPrefix (n : ℕ) (C : Circuit) (cuts : Cuts) (k a b w : ℕ) : Circuit :=
  ⟨(build n C cuts k).gates ++ [⟨.and,[a,w]⟩,⟨.and,[b,w]⟩],n+rank n C cuts k+1⟩

theorem cap_prefix_spec {n k : ℕ} (C : Circuit) (cuts : Cuts) (ao : IsAO2 n C)
    (hk : k ≤ C.gates.length) (a b w : Fin (n+rank n C cuts k)) :
    let D := capPrefix n C cuts k a b w
    let base := actualC n C cuts k
    IsAO2 n D ∧ D.size = rank n C cuts k+2 ∧
    (∀ u : Fin (n+rank n C cuts k), ∀ x, W n D x u = W n base x u) ∧
    (∀ x, W n D x (n+rank n C cuts k) = (W n base x a && W n base x w)) ∧
    (∀ x, W n D x (n+rank n C cuts k+1) = (W n base x b && W n base x w)) := by
  obtain ⟨p,hp⟩ := pack_exists C cuts ao k hk
  have len := congrArg List.length hp
  let v (i : Fin (n+rank n C cuts k)) : p.Wire := ⟨i.val,by rw [len];exact i.isLt⟩
  let q := p.emit true (v a) (v w)
  let old (i : Fin (n+rank n C cuts k)) := p.lift true (v a) (v w) (v i)
  let pack := q.emit true (old b) (old w)
  let out := q.last true (old b) (old w)
  let D := capPrefix n C cuts k a b w
  have eo : out.val = n+rank n C cuts k+1 := by
    change n+q.gates.length = _
    simp [q,len,Nat.add_assoc]
  have eg : pack.gates = D.gates := by
    change (p.gates ++ [⟨.and,[a.val,w.val]⟩]) ++ [⟨.and,[b.val,w.val]⟩] = _
    rw [hp,List.append_assoc] <;> rfl
  have ec : pack.finish out = D := by
    change Circuit.mk pack.gates out.val = Circuit.mk D.gates D.output
    rw [eo,eg] <;> rfl
  have baseVal (u : Fin (n+rank n C cuts k)) (x : Fin n → Bool) :
      p.val (v u) x = W n (actualC n C cuts k) x u := by
    change (Circuit.wires ⟨p.gates,0⟩ (List.ofFn x)).getD u.val false = _
    rw [hp] <;> rfl
  have phys (i : pack.Wire) (x : Fin n → Bool) : W n D x i.val = pack.val i x := by
    change (Circuit.wires ⟨D.gates,D.output⟩ (List.ofFn x)).getD i.val false = _
    change ((D.gates.foldl _ (List.ofFn x)).getD i.val false) = _
    rw [←eg] <;> rfl
  have da : IsAO2 n D := by rw [←ec]; exact pack.finish_ao2 out
  refine ⟨da, by simp [D,capPrefix,Circuit.size,rank],?_,?_,?_⟩
  · intro u x
    let i := q.lift true (old b) (old w) (old u)
    have h := phys i x
    have hv : pack.val i x = p.val (v u) x := by simp [pack,i,q,old]
    rw [hv,baseVal] at h
    exact h
  · intro x
    let i := q.lift true (old b) (old w) (p.last true (v a) (v w))
    have h := phys i x
    have hv : pack.val i x = (p.val (v a) x && p.val (v w) x) := by simp [pack,i,q]
    have idx : i.val = n+rank n C cuts k := by change n+p.gates.length = _;rw [len]
    rw [idx,hv,baseVal,baseVal] at h
    exact h
  · intro x
    have h := phys out x
    have hv : pack.val out x = (p.val (v b) x && p.val (v w) x) := by simp [pack,out,q,old]
    rw [eo,hv,baseVal,baseVal] at h
    exact h
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
