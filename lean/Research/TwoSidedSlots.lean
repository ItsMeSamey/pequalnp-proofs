import Research.SharedLocalSlots
import Research.RegularMatchingDecomposition

namespace TwoSidedSlots
open SharedLocalSlots

def ColumnLocal {n : ℕ} (I : Fin n → Fin n → Prop) (l : Fin n) (e : Expr) :=
  (∃ a b : ℕ, a ≠ b ∧ hit a l.val e ∧ hit b l.val e) ∧
  ∀ a, hit a l.val e → ∃ p : Fin n, p.val=a ∧ I p l

noncomputable def column_list {n : ℕ} (I : Fin n → Fin n → Prop) (l : Fin n) (e : Expr) :
    List Expr := by
  classical
  exact (gates e).filter (fun g => decide (ColumnLocal I l g))

private theorem col_hit (f : ℕ → ℕ → ℕ) (n j p l : ℕ) (e : Expr)
    (hg : e ∈ gates (col f j n)) (h : hit p l e) : p<n ∧ f p j=l := by
  induction n with
  | zero =>
    have : e = .zero := by simpa [col,gates] using hg
    subst e; exact False.elim h
  | succ n ih =>
    change e ∈ gates (.join _ _) at hg
    simp only [gates,List.mem_append,List.mem_cons,List.not_mem_nil,or_false,false_or] at hg
    rcases hg with (old|rfl)|rfl
    · obtain ⟨lim,eq⟩ := ih old
      exact ⟨by omega,eq⟩
    · change n=p ∧ f n j=l at h
      obtain ⟨rfl,eq⟩ := h
      exact ⟨by omega,eq⟩
    · obtain ⟨a,ha,rfl,h'⟩ := (col_eval f (n+1) j (· = p) (· = l)).mp h
      exact ⟨ha,h'⟩

theorem example_formula {q n : ℕ} (I : Fin n → Fin n → Prop) [DecidableRel I]
    (row : ∀ p, Fintype.card {l // I p l}=q+1)
    (column : ∀ l, Fintype.card {p // I p l}=q+1) (hq : 0<q) :
    ∃ f : ℕ → ℕ → ℕ,
      (∀ x y : ℕ → Prop, eval x y (top f n q) ↔ ∃ p l : Fin n, I p l ∧ x p.val ∧ y l.val) ∧
      (∀ p : Fin n, ∀ l : ℕ, (∃ j ≤ q, f p.val j=l) ↔ ∃ k : Fin n, I p k ∧ k.val=l) ∧
      (∀ p : Fin n, row_local_list f q p.val (top f n q) = merges f n q) ∧
      (∀ l : Fin n, column_list I l (top f n q) = merges f n q) ∧
      (merges f n q).length=q := by
  classical
  obtain ⟨M,inj,covers⟩ := RegularMatchingDecomposition.decompose (q+1) I row column
  let f (p j : ℕ) := if hp : p<n then if hj : j<q+1 then
    (M ⟨j,hj⟩ ⟨p,hp⟩).val else 0 else 0
  have entry (p : Fin n) (j : Fin (q+1)) : f p.val j.val = (M j p).val := by
    simp [f,p.isLt,j.isLt]
  have eqv (p : Fin n) (l : ℕ) : (∃ j ≤ q, f p.val j=l) ↔ ∃ k : Fin n, I p k ∧ k.val=l := by
    constructor
    · rintro ⟨j,hj,h⟩
      let z : Fin (q+1) := ⟨j,by omega⟩
      exact ⟨M z p,(covers _ _).mpr ⟨z,rfl⟩,(entry p z).symm.trans h⟩
    · rintro ⟨k,h,eq⟩
      obtain ⟨j,hj⟩ := (covers p k).mp h
      exact ⟨j,by have := j.isLt; omega,(entry p j).trans ((congrArg Fin.val hj).trans eq)⟩
  let j0 : Fin (q+1) := ⟨0,by omega⟩
  let j1 : Fin (q+1) := ⟨1,by omega⟩
  have j01 : j0 ≠ j1 := by intro h; exact Nat.zero_ne_one (congrArg Fin.val h)
  refine ⟨f,?_,eqv,?_,?_,merge_count _ _ _⟩
  · intro x y; rw [top_eval]
    constructor
    · rintro ⟨j,hj,p,hp,hx,hy⟩
      let a : Fin n := ⟨p,hp⟩
      obtain ⟨l,h,e⟩ := (eqv a _).mp ⟨j,hj,rfl⟩
      exact ⟨a,l,h,hx,e ▸ hy⟩
    · rintro ⟨p,l,h,hx,hy⟩
      obtain ⟨j,hj,e⟩ := (eqv p l.val).mpr ⟨l,h,rfl⟩
      exact ⟨j,hj,p.val,p.isLt,hx,e ▸ hy⟩
  · intro p
    apply all_local_coincide _ _ _ _ _ p.isLt le_rfl
    intro e
    exact j01 (inj p (Fin.ext ((entry p j0).symm.trans (e.trans (entry p j1)))))
  · intro l
    have colEmpty (j : ℕ) (hj : j≤q) :
        (gates (col f j n)).filter (fun g => decide (ColumnLocal I l g)) = [] := by
      apply List.filter_eq_nil_iff.mpr
      intro g hg
      simp only [decide_eq_true_eq]
      rintro ⟨⟨a,b,ab,ha,hb⟩,_⟩
      obtain ⟨aa,ea⟩ := col_hit f n j a l.val g hg ha
      obtain ⟨bb,eb⟩ := col_hit f n j b l.val g hg hb
      let z : Fin (q+1) := ⟨j,by omega⟩
      have eq : M z ⟨a,aa⟩ = M z ⟨b,bb⟩ := Fin.ext
        ((entry ⟨a,aa⟩ z).symm.trans ((ea.trans eb.symm).trans (entry ⟨b,bb⟩ z)))
      exact ab (congrArg Fin.val ((M z).injective eq))
    have merged (k : ℕ) (hk : k+1≤q) : ColumnLocal I l (top f n (k+1)) := by
      let a := (M j0).symm l
      let b := (M j1).symm l
      have separated : a.val ≠ b.val := fun h => j01
        (RegularMatchingDecomposition.inverse_injective M inj l (Fin.ext h))
      have hitA (z : Fin (q+1)) (hz : z.val ≤ k+1) : hit ((M z).symm l).val l.val (top f n (k+1)) := by
        apply (top_eval _ _ _ _ _).mpr
        refine ⟨z.val,hz,_,((M z).symm l).isLt,rfl,?_⟩
        simpa using entry ((M z).symm l) z
      refine ⟨⟨a.val,b.val,separated,hitA j0 (Nat.zero_le _),hitA j1 (Nat.succ_le_succ (Nat.zero_le _))⟩,?_⟩
      intro u hit'
      obtain ⟨j,hj,p,hp,rfl,eq⟩ := (top_eval _ _ _ _ _).mp hit'
      let z : Fin (q+1) := ⟨j,by omega⟩
      let a' : Fin n := ⟨p,hp⟩
      exact ⟨a',rfl,(covers a' l).mpr ⟨z,Fin.ext ((entry a' z).symm.trans eq)⟩⟩
    have all (k : ℕ) (hk : k≤q) : column_list I l (top f n k) = merges f n k := by
      induction k with
      | zero => exact colEmpty 0 (by omega)
      | succ k ih =>
        have good := merged k hk
        unfold column_list at ih ⊢
        change (gates (top f n k) ++ gates (col f (k+1) n) ++ [top f n (k+1)]).filter _ = _
        simp [List.filter_append,ih (by omega),colEmpty _ hk,good,merges]
    exact all q le_rfl

end TwoSidedSlots
