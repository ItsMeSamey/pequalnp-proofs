import ThresholdUpperAverage
import Mathlib.Data.Finset.Sigma
namespace ThresholdUpperCatalogue
open scoped BigOperators
variable {V : Type*} [DecidableEq V]

def edgeUniverse (U : Finset V) := U.powersetCard 2
abbrev Name (V : Type*) := Σ _ : V,Finset V
def stars (U : Finset V) (k : Nat) : Finset (Name V) :=
  U.sigma (fun c => (U.erase c).powersetCard k)
def spokes (c : V) (leaves : Finset V) : Finset (Finset V) :=
  leaves.image (fun x => {c,x})
def star (s : Name V) := spokes s.1 s.2

theorem stars_card (U : Finset V) (k : Nat) :
    (stars U k).card=U.card*(U.card-1).choose k := by
  classical
  unfold stars
  rw [Finset.card_sigma]
  calc
    _ = ∑ _c∈U,(U.card-1).choose k := by
      apply Finset.sum_congr rfl
      intro c hc
      simp [Finset.card_powersetCard,Finset.card_erase_of_mem hc]
    _ = _ := by simp

private theorem spokes_card (c : V) (L : Finset V) (out : c∉L) :
    (spokes c L).card=L.card := by
  classical
  apply Finset.card_image_of_injOn
  intro x hx y hy eq
  change ({c,x} : Finset V)={c,y} at eq
  have mem : x∈({c,y} : Finset V) := by rw [←eq]; simp
  rcases Finset.mem_insert.mp mem with same | last
  · exact (out (same ▸ hx)).elim
  · exact Finset.mem_singleton.mp last

private theorem spokes_sub (U : Finset V) (c : V) (L : Finset V)
    (hc : c∈U) (hl : L⊆U) (out : c∉L) : spokes c L ⊆ edgeUniverse U := by
  classical
  intro e he
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
  have ne : c≠x := fun eq => out (eq.symm ▸ hx)
  exact Finset.mem_powersetCard.mpr ⟨by
    intro v hv
    rcases Finset.mem_insert.mp hv with rfl|h
    · exact hc
    · obtain rfl := Finset.mem_singleton.mp h; exact hl hx,by simp [ne]⟩

theorem star_spec (U : Finset V) (k) (s : Name V) (hs : s∈stars U k) :
    star s⊆edgeUniverse U ∧ (star s).card=k := by
  obtain ⟨c,l⟩ := s
  obtain ⟨hc,h⟩ := Finset.mem_sigma.mp hs
  obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp h
  have out : c∉l := fun h => Finset.notMem_erase c U (sub h)
  exact ⟨spokes_sub U c l hc (sub.trans (Finset.erase_subset _ _)) out,
    (spokes_card c l out).trans sz⟩

/- The smallest vertex in a four-set has three possible opposite vertices.
Choosing its opposite specifies an undirected cycle with no orientation multiplicity. -/
variable [LinearOrder V]
abbrev CycleName (V : Type*) := Σ _ : Finset V,V
noncomputable def anchor (Q : Finset V) (fallback : V) :=
  if h : Q.Nonempty then Q.min' h else fallback

noncomputable def opposites (Q : Finset V) : Finset V :=
  if h : Q.Nonempty then Q.erase (Q.min' h) else ∅
noncomputable def cycles (U : Finset V) : Finset (CycleName V) :=
  (U.powersetCard 4).sigma opposites
noncomputable def cycle (s : CycleName V) : Finset (Finset V) :=
  let c := anchor s.1 s.2
  let L := (s.1.erase c).erase s.2
  spokes c L ∪ spokes s.2 L

theorem cycles_card (U : Finset V) : (cycles U).card=U.card.choose 4*3 := by
  classical
  unfold cycles
  rw [Finset.card_sigma]
  calc
    _ = ∑ _Q∈U.powersetCard 4,3 := by
      apply Finset.sum_congr rfl
      intro Q hQ
      have sz := (Finset.mem_powersetCard.mp hQ).2
      have ne : Q.Nonempty := Finset.card_pos.mp (by omega)
      simp [opposites,ne,Finset.card_erase_of_mem (Q.min'_mem ne),sz]
    _ = _ := by simp [Finset.card_powersetCard]

theorem cycle_spec (U : Finset V) (s : CycleName V) (hs : s∈cycles U) :
    cycle s⊆edgeUniverse U ∧ (cycle s).card=4 := by
  classical
  obtain ⟨Q,d⟩ := s
  obtain ⟨q,h⟩ := Finset.mem_sigma.mp hs
  change Q∈U.powersetCard 4 at q
  obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp q
  have ne : Q.Nonempty := Finset.card_pos.mp (by omega)
  let c := Q.min' ne
  have hc : c∈Q := Q.min'_mem ne
  have hd : d∈Q.erase c := by simpa [opposites,ne,c] using h
  let L := (Q.erase c).erase d
  have dc := (Finset.mem_erase.mp hd).1
  have ls : L⊆Q := (Finset.erase_subset _ _).trans (Finset.erase_subset _ _)
  have nc : c∉L := fun e => Finset.notMem_erase c Q ((Finset.erase_subset _ _ ) e)
  have nd : d∉L := Finset.notMem_erase _ _
  have card : L.card=2 := by simp [L,Finset.card_erase_of_mem hd,Finset.card_erase_of_mem hc,sz]
  have dis : Disjoint (spokes c L) (spokes d L) := by
    apply Finset.disjoint_left.mpr
    intro e left right
    obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp left
    obtain ⟨y,hy,eq⟩ := Finset.mem_image.mp right
    have dmem : d∈({c,x} : Finset V) := eq ▸ (by simp : d∈({d,y} : Finset V))
    rcases Finset.mem_insert.mp dmem with same|last
    · exact dc same
    · exact nd ((Finset.mem_singleton.mp last).symm ▸ hx)
  have same : cycle ⟨Q,d⟩=spokes c L∪spokes d L := by simp [cycle,anchor,ne,c,L]
  rw [same,Finset.card_union_of_disjoint dis,spokes_card c L nc,spokes_card d L nd,card]
  exact ⟨Finset.union_subset (spokes_sub U c L (sub hc) (ls.trans sub) nc)
    (spokes_sub U d L (sub (Finset.mem_erase.mp hd).2) (ls.trans sub) nd),rfl⟩

/-- A degree cap stated for the actual sampled edge set. -/
def neighbors (U : Finset V) (R : Finset (Finset V)) (c : V) :=
  (U.erase c).filter (fun x => ({c,x} : Finset V)∈R)

theorem no_star_degree (U : Finset V) (R : Finset (Finset V)) (k : Nat)
    (absent : ∀ s∈stars U k,¬star s⊆R) (c : V) (hc : c∈U) :
    (neighbors U R c).card<k := by
  classical
  by_contra! le
  obtain ⟨L,sub,size⟩ := Finset.exists_subset_card_eq le
  have named : (⟨c,L⟩ : Name V)∈stars U k := Finset.mem_sigma.mpr
    ⟨hc,Finset.mem_powersetCard.mpr ⟨sub.trans (Finset.filter_subset _ _),size⟩⟩
  apply absent _ named
  intro e he
  obtain ⟨x,hx,rfl⟩ := Finset.mem_image.mp he
  exact (Finset.mem_filter.mp (sub hx)).2

theorem select (U : Finset V) (v k : Nat) (four : 4≤v) (kf : k≤v)
    (room : (U.card*(U.card-1).choose k)*((U.card.choose 2)-k).choose (v-k)<
      (U.card.choose 2).choose v) :
    ∃ R∈(edgeUniverse U).powersetCard v,
      (∀ c∈U,(neighbors U R c).card<k) ∧
      ((U.card.choose 2).choose v-(U.card*(U.card-1).choose k)*((U.card.choose 2)-k).choose (v-k))*
        (((stars U 2).filter (fun s => star s⊆R)).card+
          ((cycles U).filter (fun s => cycle s⊆R)).card) ≤
      (U.card*(U.card-1).choose 2)*((U.card.choose 2)-2).choose (v-2)+
      (U.card.choose 4*3)*((U.card.choose 2)-4).choose (v-4) := by
  classical
  obtain ⟨R,mem,no,cap⟩ := ThresholdUpperAverage.first_selection (edgeUniverse U) v k four kf
    (stars U 2) (cycles U) (stars U k) star cycle star
    (star_spec U 2) (cycle_spec U) (star_spec U k)
    (by simpa [edgeUniverse,stars_card,Finset.card_powersetCard] using room)
  exact ⟨R,mem,no_star_degree U R k no,by
    simpa [edgeUniverse,stars_card,cycles_card,Finset.card_powersetCard] using cap⟩

end ThresholdUpperCatalogue
