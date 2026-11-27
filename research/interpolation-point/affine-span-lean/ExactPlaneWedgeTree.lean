import ExactPlaneWedgeProduct
namespace ExactPlaneWedgeTree
open ExactPlaneWedgeProduct
open Submodule
variable {n : ℕ}
inductive Tree (n : ℕ)
  | leaf (site : Fin n)
  | join (left right : Tree n)

def leaves : Tree n → Finset (Fin n)
  | .leaf i => {i}
  | .join l r => leaves l ∪ leaves r

def separated : Tree n → Prop
  | .leaf _ => True
  | .join l r => Disjoint (leaves l) (leaves r) ∧ separated l ∧ separated r

def combine {P Q : Type*} (ok : P→Q→Prop)
    (L : P→Set (Feature n)) (R : Q→Set (Feature n)) : Set (Feature n) :=
  ⋃ t : {t : P×Q // ok t.1 t.2}, Set.image2 (fun a b=>bilinear n a b) (L t.val.1) (R t.val.2)

theorem mem_combine {P Q : Type*} (ok : P→Q→Prop) (L : P→Set (Feature n)) (R : Q→Set (Feature n))
    (z : Feature n) : z∈combine ok L R ↔
    ∃ i j,ok i j ∧ ∃ x∈L i, ∃ y∈R j, bilinear n x y=z := by
  constructor
  · intro hz
    obtain ⟨t,x,hx,y,hy,eq⟩ := Set.mem_iUnion.mp hz
    exact ⟨_,_,t.property,x,hx,y,hy,eq⟩
  · rintro ⟨i,j,ij,x,hx,y,hy,eq⟩
    exact Set.mem_iUnion.mpr ⟨⟨(i,j),ij⟩,x,hx,y,hy,eq⟩

theorem combine_span {P Q : Type*} (ok : P→Q→Prop)
    (L L' : P→Set (Feature n)) (R R' : Q→Set (Feature n))
    (hl : ∀ i,span F (L' i)=span F (L i)) (hr : ∀ i,span F (R' i)=span F (R i)) :
    span F (combine ok L' R') = span F (combine ok L R) := by
  unfold combine
  simp only [span_iUnion]
  exact iSup_congr fun t => retained_span _ _ _ _ (hl t.val.1) (hr t.val.2)

noncomputable def thin (S : Set (Feature n)) : Finset (Feature n) :=
  Classical.choose (retain id S.toFinite.toFinset)

theorem thin_spec (S : Set (Feature n)) :
    (thin S : Set (Feature n)) ⊆ S ∧ LinearIndepOn F id (thin S : Set (Feature n)) ∧
      span F (thin S : Set (Feature n)) = span F S := by
  classical
  obtain ⟨sub,li,sp⟩ := Classical.choose_spec (retain id S.toFinite.toFinset)
  refine ⟨?_,li,?_⟩
  · intro x hx
    exact S.toFinite.mem_toFinset.mp (sub hx)
  · simpa only [thin,Set.image_id,Set.Finite.coe_toFinset] using sp

variable (State : Tree n→Type*) (base : (i : Fin n)→State (.leaf i)→Set (Feature n))
  (merge : (l r : Tree n)→State (.join l r)→State l→State r→Prop)

noncomputable def run : (t : Tree n)→State t→Finset (Feature n)
  | .leaf i,s => thin (base i s)
  | .join l r,s => thin (combine (merge l r s) (fun x => (run l x : Set _)) (fun y => (run r y : Set _)))

theorem run_exact (physical : (t : Tree n)→State t→Set (Feature n))
    (leaf : ∀ i s,base i s=physical (.leaf i) s)
    (join : ∀ l r,Disjoint (leaves l) (leaves r) → ∀ s,
      combine (merge l r s) (physical l) (physical r)=physical (.join l r) s)
    (t : Tree n) (sep : separated t) (s : State t) :
    (run State base merge t s : Set (Feature n)) ⊆ physical t s ∧
    LinearIndepOn F id (run State base merge t s : Set (Feature n)) ∧
    span F (run State base merge t s : Set (Feature n))=span F (physical t s) := by
  induction t with
  | leaf i => simpa only [run,←leaf] using thin_spec (base i s)
  | join l r ihl ihr =>
    let L := fun x => (run State base merge l x : Set (Feature n))
    let R := fun y => (run State base merge r y : Set (Feature n))
    let ok := merge l r s
    have real := join l r sep.1 s
    obtain ⟨sub,li,sp⟩ := thin_spec (combine ok L R)
    refine ⟨?_,li,?_⟩
    · rw [←real]
      intro z hz
      obtain ⟨i,j,hij,x,hx,y,hy,eq⟩ := (mem_combine ok L R z).mp (sub hz)
      exact (mem_combine _ _ _ _).mpr ⟨i,j,hij,x,(ihl sep.2.1 i).1 hx,y,(ihr sep.2.2 j).1 hy,eq⟩
    · exact sp.trans ((combine_span ok (physical l) L (physical r) R
        (fun i => (ihl sep.2.1 i).2.2) (fun i => (ihr sep.2.2 i).2.2)).trans
        (congrArg (span F) real))

#print axioms run_exact
end ExactPlaneWedgeTree
