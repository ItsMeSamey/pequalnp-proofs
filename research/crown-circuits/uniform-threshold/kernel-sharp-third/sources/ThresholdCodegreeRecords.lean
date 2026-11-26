import ThresholdFourSetOccupancy
import Mathlib.Data.Finset.Powerset
import Mathlib.Tactic.FinCases
open scoped BigOperators
namespace ThresholdCodegreeRecords
variable {V : Type*} [DecidableEq V]

/-- p is the marked diagonal and r is the unordered pair of common neighbors. -/
def Cross (G : SimpleGraph V) (p r : Finset V) : Prop :=
  ∀ a ∈ p, ∀ b ∈ r, G.Adj a b

def Record (G : SimpleGraph V) :=
  {z : Finset V × Finset V // z.1.card=2 ∧ z.2.card=2 ∧ Cross G z.1 z.2}

/-- Selecting a marked diagonal in a four-set determines the complementary
pairing. Its two other perfect matchings are present exactly when Cross holds. -/
def Marked (G : SimpleGraph V) (F : Finset V) :=
  {p : Finset V // p⊆F ∧ p.card=2 ∧ Cross G p (F \ p)}

private theorem marked_heq (G : SimpleGraph V) {F T : Finset V} (eq : F=T)
    (p : Marked G F) (q : Marked G T) (v : p.val=q.val) : HEq p q := by
  subst T
  exact heq_of_eq (Subtype.ext v)

def recordsEquiv (G : SimpleGraph V) :
    Record G ≃ (Σ F : {F : Finset V // F.card=4}, Marked G F.val) where
  toFun z := by
    obtain ⟨⟨p,r⟩,hp,hr,cross⟩ := z
    have dis : Disjoint p r := Finset.disjoint_left.mpr
      (fun a ha hb => (cross a ha a hb).ne rfl)
    have hF : (p ∪ r).card=4 := by rw [Finset.card_union_of_disjoint dis,hp,hr]
    have rest : (p∪r) \ p=r := by
      ext i
      simp only [Finset.mem_sdiff,Finset.mem_union]
      constructor
      · rintro ⟨h,hn⟩; exact h.resolve_left hn
      · intro h; exact ⟨Or.inr h,fun h' => Finset.disjoint_left.mp dis h' h⟩
    exact ⟨⟨p∪r,hF⟩,⟨p,Finset.subset_union_left,hp,by rwa [rest]⟩⟩
  invFun z := by
    obtain ⟨⟨F,hF⟩,⟨p,inside,hp,cross⟩⟩ := z
    refine ⟨⟨p,F \ p⟩,hp,?_,cross⟩
    rw [Finset.card_sdiff_of_subset inside,hF,hp]
  left_inv := by
    rintro ⟨⟨p,r⟩,hp,hr,cross⟩
    apply Subtype.ext
    change (p,(p∪r) \ p)=(p,r)
    congr 1
    ext a
    simp only [Finset.mem_sdiff,Finset.mem_union]
    constructor
    · rintro ⟨h,hn⟩; exact h.resolve_left hn
    · intro h; exact ⟨Or.inr h,fun hp => (cross a hp a h).ne rfl⟩
  right_inv := by
    rintro ⟨⟨F,hF⟩,⟨p,inside,hp,cross⟩⟩
    have union_eq : p∪(F \ p)=F := by
      ext a
      simp only [Finset.mem_union,Finset.mem_sdiff]
      constructor
      · rintro (h|h); exact inside h; exact h.1
      · intro h; by_cases k : a∈p
        · exact Or.inl k
        · exact Or.inr ⟨h,k⟩
    apply Sigma.ext (Subtype.ext union_eq)
    exact marked_heq G union_eq _ _ rfl

/-- The mark test is unchanged under the global bijection. Restriction thus
also gives the nonedge version. -/
theorem preserves_mark (G : SimpleGraph V) (z : Record G) :
    ((recordsEquiv G z).2).val = z.val.1 := by
  rcases z with ⟨⟨p,r⟩,hp,hr,h⟩
  rfl

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

def neighbors (p : Finset V) := Finset.univ.filter (fun b => ∀ a∈p, G.Adj a b)

def CodegreeChoice := Σ p : {p : Finset V // p.card=2},
  ↥((neighbors G p.val).powersetCard 2)

def choicesEquiv : CodegreeChoice G ≃ Record G where
  toFun z := by
    obtain ⟨⟨p,hp⟩,⟨r,hr⟩⟩ := z
    obtain ⟨sub,hc⟩ := Finset.mem_powersetCard.mp hr
    exact ⟨(p,r),hp,hc,fun a ha b hb => (Finset.mem_filter.mp (sub hb)).2 a ha⟩
  invFun z := by
    obtain ⟨⟨p,r⟩,hp,hr,h⟩ := z
    exact ⟨⟨p,hp⟩,⟨r,Finset.mem_powersetCard.mpr
      ⟨fun b hb => Finset.mem_filter.mpr ⟨Finset.mem_univ _,fun a ha => h a ha b hb⟩,hr⟩⟩⟩
  left_inv := by rintro ⟨⟨p,hp⟩,⟨r,hr⟩⟩; rfl
  right_inv := by rintro ⟨⟨p,r⟩,hp,hr,h⟩; rfl

def globalEquiv := (choicesEquiv G).trans (recordsEquiv G)

open ThresholdFourSetOccupancy

/-- Label the six edges by the incidences in a local occupancy record. -/
def edgeBit (x : Quad) (i j : Fin 4) : Bool :=
  if i=j then false else
  match min i.val j.val, max i.val j.val with
  | 0,1 => x.ab
  | 0,2 => x.ac
  | 0,3 => x.ad
  | 1,2 => x.bc
  | 1,3 => x.bd
  | _,_ => x.cd

def options (x : Quad) (nonedge : Bool) : Finset (Finset (Fin 4)) :=
  (Finset.univ.powersetCard 2).filter (fun p =>
    (∀ i∈p, ∀ j : Fin 4, j∉p → edgeBit x i j=true) ∧
    (nonedge=true → ∀ i∈p, ∀ j∈p, edgeBit x i j=false))

theorem options_card (x : Quad) :
    (options x false).card=diagonals x ∧ (options x true).card=nonedge x := by
  obtain ⟨a,b,c,d,e,f⟩ := x
  cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases f <;> decide

def clean (p : Finset V) : Prop := ∀ a∈p, ∀ b∈p, ¬G.Adj a b

private theorem adjacency_bits {F : Finset V} (e : Fin 4 ≃ ↥F) (i j : Fin 4) :
    edgeBit (ofGraph G (e 0).val (e 1).val (e 2).val (e 3).val) i j=true ↔
      G.Adj (e i).val (e j).val := by
  fin_cases i <;> fin_cases j <;> simp [edgeBit,ofGraph,SimpleGraph.adj_comm] <;> exact ⟨SimpleGraph.Adj.symm,SimpleGraph.Adj.symm⟩

/-- Transport a marked complementary diagonal through any chart of the four-set.
The optional boolean restricts the very same transport to nonedge marks. -/
noncomputable def chartEquiv (F : Finset V) (e : Fin 4 ≃ ↥F) (onlyNonedge : Bool) :
    {p : Marked G F // onlyNonedge=true → clean G p.val} ≃
      ↥(options (ofGraph G (e 0).val (e 1).val (e 2).val (e 3).val) onlyNonedge) := by
  classical
  let f := e.toEmbedding.trans (Function.Embedding.subtype (·∈F))
  let pull := fun p : Finset V => Finset.univ.filter (fun i : Fin 4 => f i∈p)
  have at_f (p : Finset V) (i : Fin 4) : i∈pull p ↔ f i∈p := by simp [pull]
  have back (p : Finset V) (sub : p⊆F) : (pull p).map f=p := by
    ext a
    constructor
    · intro h
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp h
      exact (at_f p i).mp hi
    · intro ha
      let i := e.symm ⟨a,sub ha⟩
      have v : f i=a := congrArg Subtype.val (e.apply_symm_apply _)
      exact Finset.mem_map.mpr ⟨i,(at_f p i).mpr (v ▸ ha),v⟩
  have forth (p : Finset (Fin 4)) : pull (p.map f)=p := by
    ext i
    simp [pull]
  let x := ofGraph G (e 0).val (e 1).val (e 2).val (e 3).val
  have bits (i j : Fin 4) : edgeBit x i j=true ↔ G.Adj (f i) (f j) := adjacency_bits G e i j
  let toLocal (z : {p : Marked G F // onlyNonedge=true → clean G p.val}) :
      ↥(options x onlyNonedge) := by
    obtain ⟨⟨p,sub,hp,cr⟩,ok⟩ := z
    refine ⟨pull p,Finset.mem_filter.mpr ⟨Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _,?_⟩,?_,?_⟩⟩
    · simpa using (congrArg Finset.card (back p sub)).trans hp
    · intro i hi j hj
      exact (bits i j).mpr (cr _ ((at_f p i).mp hi) _ (Finset.mem_sdiff.mpr
        ⟨(e j).property,fun h => hj ((at_f p j).mpr h)⟩))
    · intro pos i hi j hj
      cases hb : edgeBit x i j
      · rfl
      · exact False.elim (ok pos _ ((at_f p i).mp hi) _ ((at_f p j).mp hj) ((bits i j).mp hb))
  let fromLocal (z : ↥(options x onlyNonedge)) :
      {p : Marked G F // onlyNonedge=true → clean G p.val} := by
    obtain ⟨p,hp⟩ := z
    obtain ⟨sz,cr,ok⟩ := Finset.mem_filter.mp hp
    have sub : p.map f⊆F := by
      intro a ha
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      exact (e i).property
    refine ⟨⟨p.map f,sub,by simpa using (Finset.mem_powersetCard.mp sz).2,?_⟩,?_⟩
    · intro a ha b hb
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨inF,outP⟩ := Finset.mem_sdiff.mp hb
      let j := e.symm ⟨b,inF⟩
      have v : f j=b := congrArg Subtype.val (e.apply_symm_apply _)
      rw [←v]
      exact (bits i j).mp (cr i hi j (fun hj => outP (Finset.mem_map.mpr ⟨j,hj,v⟩)))
    · intro pos a ha b hb adj
      obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp ha
      obtain ⟨j,hj,rfl⟩ := Finset.mem_map.mp hb
      have off := ok pos i hi j hj
      exact Bool.noConfusion (off.symm.trans ((bits i j).mpr adj))
  exact ⟨toLocal,fromLocal,fun z => Subtype.ext (Subtype.ext (back _ z.val.property.1)),
    fun z => Subtype.ext (forth _)⟩
/-- A single marked-record reindexing, valid both for all unordered diagonals
and for nonedges only. Supplying charts requires only a labelling per four-set. -/
noncomputable def reindex (flag : Bool)
    (chart : (F : {F : Finset V // F.card=4}) → Fin 4 ≃ ↥F.val) :
    {z : CodegreeChoice G // flag=true → clean G z.1.val} ≃
    (Σ F : {F : Finset V // F.card=4},
        ↥(options (ofGraph G (chart F 0).val (chart F 1).val
          (chart F 2).val (chart F 3).val) flag)) := by
  let e := globalEquiv G
  have mark (z : CodegreeChoice G) : (e z).2.val=z.1.val := by
    rcases z with ⟨⟨p,hp⟩,⟨r,hr⟩⟩
    rfl
  let middle := Σ F : {F : Finset V // F.card=4},
    {p : Marked G F.val // flag=true → clean G p.val}
  have forget_inj : Function.Injective (fun z : middle =>
      (⟨z.1,z.2.val⟩ : Σ F : {F : Finset V // F.card=4}, Marked G F.val)) := by
    rintro ⟨F,p,hp⟩ ⟨T,q,hq⟩ eq
    cases eq
    rfl
  let lift : {z : CodegreeChoice G // flag=true → clean G z.1.val} ≃ middle := {
    toFun := fun z => ⟨(e z.val).1,(e z.val).2,by rw [mark]; exact z.property⟩
    invFun := fun z => ⟨e.symm ⟨z.1,z.2.val⟩,by
      rw [←mark,e.apply_symm_apply]
      exact z.2.property⟩
    left_inv := fun z => Subtype.ext (e.symm_apply_apply z.val)
    right_inv := by
      rintro ⟨F,p,hp⟩
      apply forget_inj
      exact e.apply_symm_apply ⟨F,p⟩ }
  exact lift.trans (Equiv.sigmaCongrRight (fun F => chartEquiv G F.val (chart F) flag))

theorem global_count (flag : Bool)
    (chart : (F : {F : Finset V // F.card=4}) → Fin 4 ≃ ↥F.val)
    [Fintype {z : CodegreeChoice G // flag=true → clean G z.1.val}] :
    Fintype.card {z : CodegreeChoice G // flag=true → clean G z.1.val} =
    ∑ F : {F : Finset V // F.card=4},
      let x := ofGraph G (chart F 0).val (chart F 1).val (chart F 2).val (chart F 3).val
      if flag then nonedge x else diagonals x := by
  classical
  rw [Fintype.card_congr (reindex G flag chart),Fintype.card_sigma]
  apply Finset.sum_congr rfl
  intro F _
  rw [Fintype.card_coe]
  cases flag
  · exact (options_card _).1
  · exact (options_card _).2

end ThresholdCodegreeRecords
