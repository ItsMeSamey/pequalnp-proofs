import Research.CrownSubcrownMarkers

namespace CrownDiagonalCharge
open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.Represents PEqualNP.Research.MissingCell

/-- Either the entire square, or a support containing at most one diagonal cell. -/
def simpleDiagonal {n : ℕ} (A : Support (Fin n)) : Prop :=
  A = Set.univ ∨ ∀ i j : Fin n, (i,i) ∈ A → (j,j) ∈ A → i=j

private theorem charged_empty_simple {n : ℕ} {A : Support (Fin n)} (h : Charged ∅ A) :
    simpleDiagonal A := by
  classical
  rcases h with ⟨r,c,rfl,_⟩ | hz
  · by_cases hr : r.Nonempty
    · obtain ⟨u,hu⟩ := hr
      exact Or.inr (fun i j hi hj => (hi.1 u hu).symm.trans (hj.1 u hu))
    · by_cases hc : c.Nonempty
      · obtain ⟨u,hu⟩ := hc
        exact Or.inr (fun i j hi hj => (hi.2 u hu).symm.trans (hj.2 u hu))
      · have er := Finset.not_nonempty_iff_eq_empty.mp hr
        have ec := Finset.not_nonempty_iff_eq_empty.mp hc
        exact Or.inl (by ext p; simp [er,ec,conjSupport])
  · exact Or.inr (fun i _ hi _ => False.elim (Finset.notMem_empty _ (hz hi)))

private theorem simple_inter {n : ℕ} {A B : Support (Fin n)} (ha : simpleDiagonal A)
    (hb : simpleDiagonal B) : simpleDiagonal (A ∩ B) := by
  rcases ha with rfl | h
  · simpa using hb
  · exact Or.inr (fun i j hi hj => h i j hi.1 hj.1)

private theorem union_full {n : ℕ} (hn : 3 ≤ n) {A B : Support (Fin n)} (ha : simpleDiagonal A)
    (hb : simpleDiagonal B) (h : ∀ i, (i,i) ∈ A ∪ B) : A ∪ B = Set.univ := by
  rcases ha with rfl | a
  · simp
  rcases hb with rfl | b
  · simp
  let i : Fin n := ⟨0,by omega⟩
  let j : Fin n := ⟨1,by omega⟩
  let k : Fin n := ⟨2,by omega⟩
  have ij : i ≠ j := by simp [i,j]
  have ik : i ≠ k := by simp [i,k]
  have jk : j ≠ k := by simp [j,k]
  exfalso
  rcases h i with hi | hi <;> rcases h j with hj | hj <;> rcases h k with hk | hk <;>
    first | exact ij (a _ _ hi hj) | exact ij (b _ _ hi hj) | exact ik (a _ _ hi hk)
          | exact ik (b _ _ hi hk) | exact jk (a _ _ hj hk) | exact jk (b _ _ hj hk)

def flatOr {n : ℕ} : List Gate → Env n → Prop
  | [], _ => True
  | g :: gs,w => (g.op = .or → diagFree (gateSupport g w) ∨ ∀ i, (i,i) ∈ gateSupport g w) ∧
      flatOr gs (push g w)

theorem flags_equal_flat {n : ℕ} (gs : List Gate) (w : Env n)
    (h : ∀ i j, trueOrFlags gs (w (i,i)) = trueOrFlags gs (w (j,j))) : flatOr gs w := by
  induction gs generalizing w with
  | nil => trivial
  | cons g gs ih =>
    constructor
    · intro ho
      by_cases any : ∃ i, (i,i) ∈ gateSupport g w
      · obtain ⟨i,hi⟩ := any
        refine Or.inr (fun j => ?_)
        have he := congrArg List.head? (h i j)
        change g.op.eval (g.inputs.map fun k => (w (i,i)).getD k false) = true at hi
        change g.op.eval (g.inputs.map fun k => (w (j,j)).getD k false) = true
        simp only [trueOrFlags,List.head?_cons, Option.some.injEq] at he
        have hg : isOrGate g = true := by simp [isOrGate,ho]
        simpa only [hg,Bool.true_and,hi,eq_comm] using he
      · exact Or.inl (fun i hi => any ⟨i,hi⟩)
    · apply ih
      intro i j
      exact congrArg List.tail (h i j)

theorem flat_trace_eval {n : ℕ} (hn : 3 ≤ n) (gs : List Gate) (w : Env n) (k m : ℕ)
    (K : Set (Support (Fin n))) (tr : Trace (Fin n) K m)
    (sa : ∀ A ∈ K, simpleDiagonal A)
    (h0 : ∅ ∈ K) (h1 : Set.univ ∈ K) (hw : ∀ i, wire w i ∈ K)
    (hl : ∀ p, (w p).length = k)
    (ha : ∀ g ∈ gs, (g.op = .and ∨ g.op = .or) ∧ g.inputs.length ≤ 2)
    (flat : flatOr gs w) :
    ∃ J : Set (Support (Fin n)), Trace (Fin n) J (m + (gs.filter isAndGate).length) ∧
      ∀ i, wire (fun p => (Circuit.mk gs i).wires (w p)) i ∈ J := by
  induction gs generalizing w k m K with
  | nil => exact ⟨K,by simpa using tr,hw⟩
  | cons g gs ih =>
    obtain ⟨hop,len⟩ := ha g (List.mem_cons_self ..)
    obtain ⟨A,hA,B,hB,han,hor⟩ := gate_args w g hw h0 h1 len hop
    obtain ⟨hd,rest⟩ := flat
    have step : ∃ T, Trace (Fin n) T (m + (if isAndGate g then 1 else 0)) ∧
        K ⊆ T ∧ gateSupport g w ∈ T ∧ ∀ X ∈ T, simpleDiagonal X := by
      rcases hop with h | h
      · rw [han h]
        refine ⟨_,by simpa [isAndGate,h] using Trace.andGate tr hA hB,Set.subset_insert ..,Set.mem_insert ..,?_⟩
        intro X hx
        rcases Set.mem_insert_iff.mp hx with rfl | old
        · exact simple_inter (sa A hA) (sa B hB)
        · exact sa _ old
      · rcases hd h with free | full
        · rw [hor h] at free ⊢
          refine ⟨_,by simpa [isAndGate,h] using Trace.orGate tr hA hB free,Set.subset_insert ..,Set.mem_insert ..,?_⟩
          intro X hx
          rcases Set.mem_insert_iff.mp hx with rfl | old
          · exact Or.inr (fun i _ hi _ => False.elim (free i hi))
          · exact sa _ old
        · have he := union_full hn (sa A hA) (sa B hB) ((hor h) ▸ full)
          exact ⟨K,by simpa [isAndGate,h] using tr,fun _ x => x,(hor h).trans he ▸ h1,sa⟩
    obtain ⟨T,tt,sub,hg,st⟩ := step
    have nextw := push_known g hl (fun i => sub (hw i)) hg
    have nextl : ∀ p, (push g w p).length = k+1 := by intro p; simp [push,hl]
    obtain ⟨J,tj,out⟩ := ih (push g w) (k+1) _ T tt st (sub h0) (sub h1) nextw nextl
      (fun a ha' => ha a (List.mem_cons_of_mem _ ha')) rest
    refine ⟨J,?_,out⟩
    cases h : isAndGate g <;> simpa [h,Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using tj

theorem uniform_subcrown_and {k n : ℕ} (hk : 3 ≤ k) (e : Fin k ↪ Fin n) (C : Circuit)
    (hm : Monotone2 C) (rep : Represents (fun u v : Fin n => decide (u ≠ v)) C)
    (flags : ∀ i j, trueOrFlags C.gates (oneEach (e i) (e i)) =
      trueOrFlags C.gates (oneEach (e j) (e j))) : k*(k-1) ≤ (C.gates.filter isAndGate).length := by
  let w := restrictEnv e
  obtain ⟨J,tr,hJ⟩ := flat_trace_eval hk C.gates w (n+n) 0 _ Trace.initial (fun _ => charged_empty_simple)
    initial_false initial_true (subset_wire_charged e) (fun p => by simp [w,restrictEnv,oneEach])
    hm (flags_equal_flat _ _ flags)
  have eq : wire (fun p => C.wires (w p)) C.output = {p : Cell (Fin k) | p.1 ≠ p.2} := by
    ext p
    change C.eval (oneEach (e p.1) (e p.2)) = true ↔ _
    rw [rep (e p.1) (e p.2)]
    simp
  have hout := hJ C.output
  change wire (fun p => C.wires (w p)) C.output ∈ J at hout
  rw [eq] at hout
  simpa using trace_crown_and_count tr hout

theorem crown_equal_signature_class_small (C : Circuit) (hm : Monotone2 C)
    (rep : Represents (fun u v : Fin 12 => decide (u ≠ v)) C)
    (size : C.size ≤ 40) (b : List Bool) :
    (Finset.univ.filter (fun i : Fin 12 => trueOrFlags C.gates (oneEach i i) = b)).card ≤ 4 := by
  classical
  let S := Finset.univ.filter (fun i : Fin 12 => trueOrFlags C.gates (oneEach i i) = b)
  let e : Fin S.card ↪ Fin 12 := (S.orderIsoOfFin rfl).toEquiv.toEmbedding.trans (Function.Embedding.subtype _)
  have he (i : Fin S.card) : trueOrFlags C.gates (oneEach (e i) (e i)) = b :=
    (Finset.mem_filter.mp ((S.orderIsoOfFin rfl i).property)).2
  change S.card ≤ 4
  by_contra! h
  have bound := uniform_subcrown_and (by omega : 3 ≤ S.card) e C hm rep (fun i j => (he i).trans (he j).symm)
  have old := crown_size_forty_requires_twenty_three_ors C hm rep size
  have part := and_or_partition C.gates (fun g hg => (hm g hg).1)
  change C.gates.length ≤ 40 at size
  have prod := Nat.mul_le_mul (show 5 ≤ S.card by omega) (show 4 ≤ S.card-1 by omega)
  omega

end CrownDiagonalCharge
