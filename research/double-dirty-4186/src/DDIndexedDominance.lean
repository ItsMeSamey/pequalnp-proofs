import DDIndexedNoOr
import DDIndexedPrefix
import DDMultiCut
namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm PEqualNP.EdgeOwnership
open PEqualNP.Outside.L_meta_4186_aux
open Q1Double S4183.S98
attribute [local instance] gateOpDecEq

theorem op_preserved {n j : ℕ} {C : Circuit} {p : Cuts} {g : Gate}
    (hg : ins n C p j = some g) : g.op = (gateAt C j).op := by
  unfold ins at hg
  cases l : pin (build n C p j) n C p j 0 <;> cases r : pin (build n C p j) n C p j 1 <;>
    cases s : p.omit j <;> simp [instruction,l,r,s] at hg
  subst g; rfl
theorem prefix_gate {n k i a b w : ℕ} {C : Circuit} {p : Cuts} {g : Gate}
    (hg : ins n C p i = some g) (hi : i < k) :
    gateAt (capPrefix n C p k a b w) (rank n C p i) = g := by
  have lt := paid_strict C p hg hi
  have atGate := retains_instruction C p hg hi
  simp only [gateAt,capPrefix,List.getD_eq_getElem?_getD,List.getElem?_append_left lt,atGate,Option.getD_some]
private theorem tail_and {n k q a b w : ℕ} {C : Circuit} {p : Cuts}
    (lo : rank n C p k ≤ q) (hi : q < (capPrefix n C p k a b w).size) :
    (gateAt (capPrefix n C p k a b w) q).op = .and := by
  have bound : q < rank n C p k+2 := by simpa [capPrefix,Circuit.size,rank] using hi
  have eq : q = rank n C p k ∨ q = rank n C p k+1 := by omega
  rcases eq with rfl | rfl <;> simp [gateAt,capPrefix,rank,List.getD_eq_getElem?_getD]
theorem cap_reader_and {n m k i j : ℕ} {G : SimpleGraph (Fin n)} [DecidableRel G.Adj] {C : Circuit}
    (hD : DoubleDirty G C m) (ao : IsAO2 n C) (hk : k ≤ C.size)
    (a b w : Fin (n+rank n C (splitCuts n C (orT G C) m) k)) :
    let cap := capPrefix n C (splitCuts n C (orT G C) m) k a b w
    (gateAt cap i).op = .and → j < cap.size → n+i ∈ (gateAt cap j).inputs → (gateAt cap j).op = .and := by
  let s := splitCuts n C (orT G C) m
  let cap := capPrefix n C s k a b w
  dsimp only
  intro hop hj hin
  change (gateAt cap j).op = .and
  by_cases pre : j < rank n C s k
  · obtain ⟨r,hr,gg,hg,eq⟩ := physical_owner C s pre
    have gate : gateAt cap j = gg := eq ▸ prefix_gate hg hr
    have ao' := (cap_prefix_spec C s ao hk a b w).1
    have earlier := ao'.2.1 j hj _ hin
    have ilt : i < rank n C s k := by omega
    obtain ⟨v,hv,gi,vi,eqi⟩ := physical_owner C s ilt
    have gati : gateAt cap i = gi := eqi ▸ prefix_gate vi hv
    have hand : (gateAt C v).op = .and := by rw [←op_preserved vi,←gati]; exact hop
    rw [gate]
    apply retained_reader_and hD ao (Nat.lt_of_lt_of_le hr hk) hand vi hg
    change n+rank n C s v ∈ gg.inputs
    rw [eqi]
    simpa only [gate] using (show n+i ∈ (gateAt cap j).inputs from hin)
  · exact tail_and (Nat.le_of_not_gt pre) hj

theorem dominated_path {n s : ℕ} (D : Circuit) (ao : IsAO2 n D)
    (closed : ∀ {i j}, (gateAt D i).op = .and → j<D.size → n+i ∈ (gateAt D j).inputs → (gateAt D j).op = .and)
    (hs : (gateAt D s).op = .and) {u : ℕ} (path : Influence n D s u) :
    ∃ j, u = n+j ∧ (gateAt D j).op = .and ∧ ∀ x, W n D x u = true → W n D x (n+s) = true := by
  induction path with
  | source => exact ⟨s,rfl,hs,fun _ h => h⟩
  | @step j w path hj pin ih =>
    obtain ⟨i,eq,hi,dom⟩ := ih
    have hand := closed hi hj (eq ▸ pin)
    obtain ⟨_,a,b,pins,ha,hb⟩ := AO_of_IsAO2 n D ao j hj
    refine ⟨j,rfl,hand,?_⟩
    intro x val
    rw [W_and n D x j hj hand a b pins ha hb,Bool.and_eq_true] at val
    apply dom x
    rw [pins] at pin
    rcases (by simpa only [List.mem_cons,List.not_mem_nil,or_false] using pin : w=a ∨ w=b) with rfl | rfl
    · exact val.1
    · exact val.2
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Indexed
