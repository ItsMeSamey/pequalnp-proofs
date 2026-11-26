import ThresholdActualColdCandidates
namespace ThresholdCompetingAlternates

variable {I V : Type*} [DecidableEq I] [DecidableEq V]
theorem complement_unique {a b d : Finset V} (twoA : a.card=2) (twoB : b.card=2)
    (twoD : d.card=2) (four : (a∪b).card=4) (same : a∪b=a∪d) : b=d := by
  have t := Finset.card_union_add_card_inter a b
  have u := Finset.card_union_add_card_inter a d
  have eb : (a∩b).card=0 := by omega
  have ed : (a∩d).card=0 := by rw [←same] at u; omega
  have bd := Finset.card_eq_zero.mp eb
  have dd := Finset.card_eq_zero.mp ed
  ext x
  constructor
  · intro h
    have hx : x∈a∪d := same ▸ Finset.mem_union_right a h
    rcases Finset.mem_union.mp hx with ha|hd
    · have no : x∈(∅ : Finset V) := bd ▸ Finset.mem_inter.mpr ⟨ha,h⟩
      simp at no
    · exact hd
  · intro h
    have hx : x∈a∪b := same.symm ▸ Finset.mem_union_right a h
    rcases Finset.mem_union.mp hx with ha|hb
    · have no : x∈(∅ : Finset V) := dd ▸ Finset.mem_inter.mpr ⟨ha,h⟩
      simp at no
    · exact hb

/-- A distinct competing physical row-pair shares neither row profile with
the first matching of a four-set. -/
theorem avoid {R : Finset I} {col : I → Finset V} (inject : Set.InjOn col (R:Set I))
    (two : ∀ r∈R,(col r).card=2) {a b c d : I}
    (ha : a∈R) (hb : b∈R) (hc : c∈R) (hd : d∈R)
    (four : (col a∪col b).card=4) (same : col a∪col b=col c∪col d)
    (diff : ({a,b}:Finset I)≠{c,d}) : col c≠col a ∧ col d≠col a := by
  constructor
  · intro eq
    have ca := inject hc ha eq
    subst c
    have bd := inject hb hd (complement_unique (two a ha) (two b hb) (two d hd) four same)
    exact diff (by rw [bd])
  · intro eq
    have da := inject hd ha eq
    subst d
    have sc : col a∪col b=col a∪col c := same.trans (Finset.union_comm _ _)
    have bc := inject hb hc (complement_unique (two a ha) (two b hb) (two c hc) four sc)
    exact diff (by rw [bc,Finset.pair_comm a c])

open PEqualNP.CircuitLowerBounds ResidualSurplus T2OrPartition T2SoleOrSplice T2CubeDeletion T2RegularOrDelete ThresholdOrExtraction
open ThresholdEffectiveColumns ThresholdActualColdCandidates

theorem native {C : Circuit} {n : Nat} (L : Layout C n) (M : LexMinimum n C)
    {R : Finset (Id C)} (G : SimpleGraph (Id C))
    (inject : Set.InjOn (effective L M) (R:Set _))
    (two : ∀ r∈R,(effective L M r).card=2)
    (adj : ∀ r∈R,∀ a b,effective L M r={a,b} → G.Adj a b)
    {p : Finset (Id C)} (mem : p∈cold L M R) {a b S : Id C}
    (eq : p={a,b}) (ha : a∈R) (hb : b∈R) (touch : S∈effective L M a) :
    ∃ T i j k l,G.Adj i j ∧ G.Adj k l ∧
      ({i,j}:Finset _)∪{k,l}={S,T}∪effective L M b ∧
      ({i,j}:Finset _)≠{S,T} ∧ ({k,l}:Finset _)≠{S,T} := by
  classical
  obtain ⟨q,pair,diff,boxeq⟩ := competitors L M mem
  obtain ⟨sub,sz⟩ := Finset.mem_powersetCard.mp pair
  obtain ⟨c,d,_,qe⟩ := Finset.card_eq_two.mp sz
  have hc := sub (show c∈q by simp [qe])
  have hd := sub (show d∈q by simp [qe])
  have four := (Finset.mem_filter.mp (Finset.mem_filter.mp mem).1).2.1
  have sz4 : (effective L M a∪effective L M b).card=4 := by simpa [box,eq] using four
  have same : effective L M a∪effective L M b=effective L M c∪effective L M d := by
    simpa [box,eq,qe] using boxeq.symm
  have different : ({a,b}:Finset _)≠{c,d} := by simpa [eq,qe] using diff.symm
  obtain ⟨one,other⟩ := avoid inject two ha hb hc hd sz4 same different
  obtain ⟨i,j,_,ce⟩ := Finset.card_eq_two.mp (two c hc)
  obtain ⟨k,l,_,de⟩ := Finset.card_eq_two.mp (two d hd)
  obtain ⟨u,v,_,ae⟩ := Finset.card_eq_two.mp (two a ha)
  have st : ∃ T,effective L M a={S,T} := by
    have hit : S=u ∨ S=v := by simpa [ae] using touch
    rcases hit with rfl|rfl
    · exact ⟨v,ae⟩
    · exact ⟨u,ae.trans (Finset.pair_comm _ _)⟩
  obtain ⟨T,ae'⟩ := st
  exact ⟨T,i,j,k,l,adj c hc i j ce,adj d hd k l de,
    by simpa only [ce,de,ae'] using same.symm,
    by simpa only [ce,ae'] using one,by simpa only [de,ae'] using other⟩

end ThresholdCompetingAlternates
