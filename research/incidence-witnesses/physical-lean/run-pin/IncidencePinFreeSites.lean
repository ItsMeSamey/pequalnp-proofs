import IncidencePinPlaneGeometry
import IncidencePinCompact
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Finset.Sum
namespace IncidencePinFreeSites
open IncidenceRobust
variable {n : Nat}

def sites (P Q : Finset (Fin n)) := (Finset.univ \ P).disjSum (Finset.univ \ Q)
def m (P Q : Finset (Fin n)) := (sites P Q).card
noncomputable def index (P Q : Finset (Fin n)) : ↥(sites P Q) ≃ Fin (m P Q) :=
  Fintype.equivFinOfCardEq (by simp [m])
noncomputable def tag (P Q : Finset (Fin n)) (i : Fin (m P Q)) : Vertex n := ((index P Q).symm i).val
noncomputable def key (P Q : Finset (Fin n)) (positive : 0<m P Q) (v : Vertex n) : Fin (m P Q) :=
  if h : v∈sites P Q then index P Q ⟨v,h⟩ else ⟨0,positive⟩

theorem left_free (P Q : Finset (Fin n)) (p : Fin n) : Sum.inl p∈sites P Q ↔ p∉P := by
  simp [sites]
theorem right_free (P Q : Finset (Fin n)) (l : Fin n) : Sum.inr l∈sites P Q ↔ l∉Q := by
  simp [sites]
theorem tag_free (P Q : Finset (Fin n)) (i : Fin (m P Q)) : tag P Q i∈sites P Q :=
  ((index P Q).symm i).property
theorem tag_key (P Q : Finset (Fin n)) (h : 0<m P Q) {v : Vertex n} (free : v∈sites P Q) :
    tag P Q (key P Q h v)=v := by simp [key,free,tag]
theorem key_tag (P Q : Finset (Fin n)) (h : 0<m P Q) (i : Fin (m P Q)) :
    key P Q h (tag P Q i)=i := by simp [key,tag_free,tag]
theorem tag_inj (P Q : Finset (Fin n)) : Function.Injective (tag P Q) :=
  Subtype.val_injective.comp (index P Q).symm.injective

theorem total (P Q : Finset (Fin n)) : m P Q=(n-P.card)+(n-Q.card) := by
  simp [m,sites,Finset.card_sdiff_of_subset]

noncomputable def raw (P Q : Finset (Fin n)) (h : 0<m P Q) (i : Nat) : Fin (m P Q) :=
  if a : i<n then key P Q h (.inl ⟨i,a⟩)
  else if b : i<n+n then key P Q h (.inr ⟨i-n,by omega⟩) else ⟨0,h⟩

theorem left (P Q : Finset (Fin n)) (h : 0<m P Q) (p : Fin n) :
    raw P Q h p.val=key P Q h (.inl p) := by simp [raw,p.isLt]
theorem right (P Q : Finset (Fin n)) (h : 0<m P Q) (l : Fin n) :
    raw P Q h (n+l.val)=key P Q h (.inr l) := by
  have lo : ¬ n+l.val<n := by omega
  have hi : n+l.val<n+n := by have := l.isLt; omega
  simp [raw,lo,hi]

variable (I : Fin n→Fin n→Prop) [DecidableRel I]
def near (P Q : Finset (Fin n)) : Vertex n → Finset (Vertex n)
  | .inl p => ((lines I p) \ Q).map Function.Embedding.inr
  | .inr l => ((points I l) \ P).map Function.Embedding.inl

theorem near_spec (P Q : Finset (Fin n)) (x y : Vertex n) :
    y∈near I P Q x ↔ y∈sites P Q ∧ Edge I x y := by
  cases x <;> cases y <;> simp [near,sites,lines,points,Edge,and_comm]

noncomputable def neighbors (P Q : Finset (Fin n)) (i : Fin (m P Q)) :=
  Finset.univ.filter (fun j : Fin (m P Q) => tag P Q j∈near I P Q (tag P Q i))

theorem neighbor_spec (P Q : Finset (Fin n)) (i j : Fin (m P Q)) :
    j∈neighbors I P Q i ↔ Edge I (tag P Q i) (tag P Q j) := by
  simp [neighbors,near_spec,tag_free]

theorem degree_eq (P Q : Finset (Fin n)) (i : Fin (m P Q)) :
    (neighbors I P Q i).card=(near I P Q (tag P Q i)).card := by
  classical
  have eq : (neighbors I P Q i).image (tag P Q)=near I P Q (tag P Q i) := by
    ext v
    constructor
    · rintro h
      obtain ⟨j,hj,rfl⟩ := Finset.mem_image.mp h
      exact (Finset.mem_filter.mp hj).2
    · intro hv
      have free := ((near_spec I P Q _ _).mp hv).1
      let j := index P Q ⟨v,free⟩
      have e : tag P Q j=v := by simp [j,tag]
      exact Finset.mem_image.mpr ⟨j,Finset.mem_filter.mpr ⟨Finset.mem_univ _,e ▸ hv⟩,e⟩
  rw [←eq,Finset.card_image_of_injective _ (tag_inj P Q)]

open IncidencePinPlaneGeometry

theorem min_degree {q : Nat} (degree : ∀ l,Fintype.card {p // I p l}=q+1)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hq : 0<q) (hn : n=q^2+q+1)
    (P : Finset (Fin n)) (i : Fin (m P (removedLines I P))) :
    q+1-P.card ≤ (neighbors I P (removedLines I P) i).card := by
  rw [degree_eq]
  have f := tag_free P (removedLines I P) i
  cases e : tag P (removedLines I P) i with
  | inl p =>
    rw [e,left_free] at f
    simpa [near] using free_point_degree I degree unique hq hn P p f
  | inr l =>
    rw [e,right_free] at f
    simp only [near,Finset.card_map,free_line_degree I degree P l f]
    omega

theorem unique_neighbor (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    {a b c d : Vertex n} (ab : a≠b) (ac : Edge I a c) (bc : Edge I b c)
    (ad : Edge I a d) (bd : Edge I b d) : c=d := by
  cases a with
  | inl p =>
    cases b with
    | inl r =>
      cases c <;> cases d <;> simp_all [Edge]
      obtain ⟨_,_,only⟩ := unique p r (by simpa using ab)
      exact (only _ ⟨ac,bc⟩).trans (only _ ⟨ad,bd⟩).symm
    | inr s => cases c <;> simp_all [Edge]
  | inr l =>
    cases b with
    | inl p => cases c <;> simp_all [Edge]
    | inr t =>
      cases c with
      | inr u => exact False.elim bc
      | inl p =>
        cases d with
        | inr u => exact False.elim ad
        | inl r =>
          by_contra ne
          obtain ⟨_,_,only⟩ := unique p r (fun e => ne (e ▸ rfl))
          exact ab (congrArg Sum.inr ((only _ ⟨ac,ad⟩).trans (only _ ⟨bc,bd⟩).symm))

theorem overlap (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l)
    (P Q : Finset (Fin n)) (x r : Fin (m P Q)) (ne : x≠r) :
    ((neighbors I P Q x) ∩ (neighbors I P Q r)).card≤1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  apply tag_inj P Q
  obtain ⟨h1,h2⟩ := Finset.mem_inter.mp ha
  obtain ⟨h3,h4⟩ := Finset.mem_inter.mp hb
  exact unique_neighbor I unique (fun e => ne (tag_inj P Q e))
    ((neighbor_spec I P Q _ _).mp h1) ((neighbor_spec I P Q _ _).mp h2)
    ((neighbor_spec I P Q _ _).mp h3) ((neighbor_spec I P Q _ _).mp h4)
end IncidencePinFreeSites
