import ThresholdGraphWedgeSum
import ThresholdSharpCodegrees
namespace ThresholdNativeGraphMoments
open ThresholdCodegreeRecords ThresholdFourSetOccupancy ThresholdGraphWedgeSum
open scoped BigOperators
variable {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V) [DecidableRel G.Adj]
noncomputable def allPairs := (Finset.univ : Finset V).powersetCard 2
noncomputable def nonedges := markedPairs G true
noncomputable def edges := allPairs (V:=V) \ nonedges G
private theorem all_false : markedPairs G false=allPairs (V:=V) := by classical ext; simp [markedPairs,allPairs]
private theorem choose_sq (k : Nat) : k^2=2*k.choose 2+k := by
  induction k with
  | zero => decide
  | succ k ih =>
    rw [Nat.choose_succ_succ]
    simp only [Nat.choose_one_right]
    nlinarith

theorem edge_count : (edges G).card=G.edgeFinset.card := by
  classical
  let label := fun e : Sym2 V => e.toFinset
  have inj : Function.Injective label := by
    intro p q eq
    apply Sym2.ext
    intro v
    simpa [label] using (congrArg (fun t : Finset V => v∈t) eq).to_iff
  have labels : G.edgeFinset.image label=edges G := by
    ext p
    constructor
    · intro hit
      obtain ⟨e,he,rfl⟩ := Finset.mem_image.mp hit
      induction e using Sym2.ind with
      | _ x y =>
        have adj : G.Adj x y := by simpa using he
        have eq : label (Sym2.mk x y)={x,y} := by simp [label,Sym2.toFinset_mk_eq]
        rw [eq]
        apply Finset.mem_sdiff.mpr
        refine ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,Finset.card_pair_eq_two_iff.mpr adj.ne⟩,?_⟩
        intro non
        have clean' := (Finset.mem_filter.mp non).2 rfl
        exact clean' x (by simp) y (by simp) adj
    · intro hit
      obtain ⟨all,notClean⟩ := Finset.mem_sdiff.mp hit
      obtain ⟨x,y,ne,rfl⟩ := Finset.card_eq_two.mp (Finset.mem_powersetCard.mp all).2
      have adj : G.Adj x y := by
        by_contra h
        apply notClean
        apply Finset.mem_filter.mpr
        refine ⟨all,fun _ a ha b hb => ?_⟩
        simp only [Finset.mem_insert,Finset.mem_singleton] at ha hb
        rcases ha with rfl|rfl <;> rcases hb with rfl|rfl <;> first | exact G.loopless.irrefl _ | exact h | exact fun e => h e.symm
      exact Finset.mem_image.mpr ⟨Sym2.mk x y,by simpa using adj,by simp [label,Sym2.toFinset_mk_eq]⟩
  rw [←labels,Finset.card_image_of_injective _ inj]

theorem first_identity :
    (∑ v,G.degree v^2)=2*(∑ p∈allPairs (V:=V),(neighbors G p).card)+2*G.edgeFinset.card := by
  classical
  let rel := fun (p : Finset V) (v : V) => ∀ x∈p,G.Adj x v
  have above (p : Finset V) : Finset.univ.bipartiteAbove rel p=neighbors G p := by ext; simp [rel,neighbors]
  have below (v : V) : (allPairs (V:=V)).bipartiteBelow rel v=(G.neighborFinset v).powersetCard 2 := by
    ext p
    simp only [Finset.mem_bipartiteBelow,allPairs,Finset.mem_powersetCard,Finset.subset_univ,true_and,rel]
    constructor
    · rintro ⟨sz,ok⟩
      exact ⟨fun x hx => (G.mem_neighborFinset _ _).mpr (ok x hx).symm,sz⟩
    · rintro ⟨ok,sz⟩
      exact ⟨sz,fun x hx => ((G.mem_neighborFinset _ _).mp (ok hx)).symm⟩
  have count := Finset.sum_card_bipartiteAbove_eq_sum_card_bipartiteBelow (s:=allPairs (V:=V)) (t:=Finset.univ) rel
  simp only [above,below,Finset.card_powersetCard,SimpleGraph.card_neighborFinset_eq_degree] at count
  simp only [choose_sq,Finset.sum_add_distrib,←Finset.mul_sum,G.sum_degrees_eq_twice_card_edges,count]

theorem moments (chart : (F : {F : Finset V // F.card=4}) → Fin 4 ≃ ↥F.val) :
    let x := fun F => ofGraph G (chart F 0).val (chart F 1).val (chart F 2).val (chart F 3).val
    let loss := ∑ F, (occupancy (x F)-1)
    let A := ∑ p∈edges G,(neighbors G p).card
    let D := ∑ p∈nonedges G,(neighbors G p).card
    let S := A+D
    let w := Fintype.card V
    let g := G.edgeFinset.card
    A^2≤g*(S+6*loss) ∧
      2*D^2≤(w*(w-1)-2*g)*(4*loss+D) ∧
      (∑ v,G.degree v^2)=2*S+2*g ∧ (2*g)^2≤w*(2*S+2*g) := by
  classical
  intro x loss A D S w g
  let c := fun p => (neighbors G p).card
  have incl : nonedges G⊆allPairs (V:=V) := Finset.filter_subset _ _
  have allSum (f : Finset V→Nat) : (∑ p∈edges G,f p)+(∑ p∈nonedges G,f p)=∑ p∈allPairs (V:=V),f p :=
    Finset.sum_sdiff incl
  have total := totals Finset.univ x
  have t := wedge_sum G false chart
  have n := wedge_sum G true chart
  rw [all_false] at t
  simp only [Bool.false_eq_true,ite_false] at t
  simp only [ite_true] at n
  have nc : (∑ p∈nonedges G,(c p).choose 2)≤2*loss := n.trans_le total.2
  have ac : (∑ p∈allPairs (V:=V),(c p).choose 2)≤3*loss := t.trans_le total.1
  have sums : (∑ p∈allPairs (V:=V),c p^2)≤(∑ p∈allPairs (V:=V),c p)+6*loss := by
    simp only [choose_sq,Finset.sum_add_distrib,←Finset.mul_sum]
    omega
  have sqs := allSum (fun p => c p^2)
  have add := allSum c
  have space := Finset.card_sdiff_add_card_eq_card incl
  change (edges G).card+(nonedges G).card=(allPairs (V:=V)).card at space
  have population : 2*((edges G).card+(nonedges G).card)≤w*(w-1) := by
    rw [space]
    simp only [allPairs,Finset.card_powersetCard,Finset.card_univ]
    change 2*w.choose 2≤w*(w-1)
    cases w with
    | zero => decide
    | succ k =>
      simp only [Nat.succ_sub_one]
      have rel := choose_sq (k+1)
      nlinarith
  have bounds := ThresholdSharpCodegrees.moments (edges G) (nonedges G) c w loss population (by omega) nc
  have count : (edges G).card=g := edge_count G
  have first : (∑ v,G.degree v^2)=2*S+2*g := (first_identity G).trans (by rw [←add])
  have cs := sq_sum_le_card_mul_sum_sq (s:=Finset.univ) (f:=fun v : V => G.degree v)
  rw [G.sum_degrees_eq_twice_card_edges,Finset.card_univ,first] at cs
  exact ⟨by simpa only [count] using bounds.1,by simpa only [count] using bounds.2,first,cs⟩

section Selected
variable {I X : Type*} [DecidableEq I] [DecidableEq X]
open ThresholdFamilySimpleGraph
open Classical in
theorem selected (R : Finset I) (col : I→Finset X)
    (two : ∀ i∈R,(col i).card=2) (inj : Set.InjOn col (R:Set I)) :
    let T := R.biUnion col
    let H := graph T (R.image col)
    let chart := fun F : {F : Finset ↥T // F.card=4} =>
      (Fintype.equivFinOfCardEq (by simpa using F.property : Fintype.card ↥F.val=4)).symm
    let loss := ∑ F, ((ThresholdEffectiveMatchingRows.fiber R col
      (Finset.univ.map (((chart F).toEmbedding.trans (Function.Embedding.subtype (·∈F.val))).trans
        (Function.Embedding.subtype (·∈T))))).card-1)
    let A := ∑ p∈edges H,(neighbors H p).card
    let D := ∑ p∈nonedges H,(neighbors H p).card
    let S := A+D
    A^2≤R.card*(S+6*loss) ∧ 2*D^2≤(T.card*(T.card-1)-2*R.card)*(4*loss+D) ∧
    (∑ v,H.degree v^2)=2*S+2*R.card ∧ (2*R.card)^2≤T.card*(2*S+2*R.card) := by
  classical
  intro T H chart loss A D S
  have valid : R.image col⊆T.powersetCard 2 := by
    intro q h
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_powersetCard.mpr ⟨fun _ hv => Finset.mem_biUnion.mpr ⟨r,hr,hv⟩,two r hr⟩
  have g : H.edgeFinset.card=R.card := (edge_card T (R.image col) valid).trans (Finset.card_image_of_injOn inj)
  have w : Fintype.card ↥T=T.card := Fintype.card_coe _
  have box (F : {F : Finset ↥T // F.card=4}) :=
    ThresholdEffectiveMatchingRows.box_graph R col T two inj
      ((chart F).toEmbedding.trans (Function.Embedding.subtype (·∈F.val)))
  have lossEq : (∑ F, (occupancy (ofGraph H (chart F 0).val (chart F 1).val
    (chart F 2).val (chart F 3).val)-1))=loss := by
    apply Finset.sum_congr rfl
    intro F _
    exact congrArg (fun k : Nat => k-1) (box F).symm
  simpa only [g,w,lossEq] using moments H chart

end Selected
#print axioms selected
end ThresholdNativeGraphMoments
