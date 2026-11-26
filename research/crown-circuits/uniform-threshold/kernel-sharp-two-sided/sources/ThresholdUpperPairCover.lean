import ThresholdUpperFourMatch
namespace ThresholdUpperCatalogue
variable {V : Type*} [LinearOrder V]

private theorem wedge_pair (U : Finset V) (a b c : V) (ab : a≠b) (ac : a≠c) (bc : b≠c)
    (ha : a∈U) (hb : b∈U) (hc : c∈U) :
    ∃ s∈stars U 2,star s=({{a,b},{a,c}} : Finset (Finset V)) := by
  classical
  refine ⟨⟨a,{b,c}⟩,Finset.mem_sigma.mpr ⟨ha,Finset.mem_powersetCard.mpr ⟨?_,by simp [bc]⟩⟩,?_⟩
  · intro v hv
    simp only [Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with rfl|rfl <;> simp_all <;> grind
  · simp [star,spokes]

private theorem disjoint_pair (U : Finset V) (a b c d : V)
    (ab : a≠b) (ac : a≠c) (ad : a≠d) (bc : b≠c) (bd : b≠d) (cd : c≠d)
    (ha : a∈U) (hb : b∈U) (hc : c∈U) (hd : d∈U) :
    ∃ Q∈U.powersetCard 4,∃ j∈opposites Q,matching Q j=({{a,b},{c,d}} : Finset (Finset V)) := by
  classical
  let Q := ({a,b,c,d} : Finset V)
  have q : Q∈U.powersetCard 4 := Finset.mem_powersetCard.mpr
    ⟨by
      intro x hx
      simp only [Q,Finset.mem_insert,Finset.mem_singleton] at hx
      rcases hx with rfl|rfl|rfl|rfl <;> assumption,by simp [Q,ab,ac,ad,bc,bd,cd]⟩
  have non : Q.Nonempty := ⟨a,by simp [Q]⟩
  have loc : Q.min' non=a ∨ Q.min' non=b ∨ Q.min' non=c ∨ Q.min' non=d := by
    simpa only [Q,Finset.mem_insert,Finset.mem_singleton] using Q.min'_mem non
  refine ⟨Q,q,?_⟩
  rcases loc with root|root|root|root
  · refine ⟨b,?_,?_⟩
    all_goals simp only [matching,anchor,opposites,dif_pos non,root]
    all_goals simp [Q,ab,ac,ad,bc,bd,cd,
      Ne.symm ab,Ne.symm ac,Ne.symm ad,Ne.symm bc,Ne.symm bd,Ne.symm cd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.pair_comm]
  · refine ⟨a,?_,?_⟩
    all_goals simp only [matching,anchor,opposites,dif_pos non,root]
    all_goals simp [Q,ab,ac,ad,bc,bd,cd,
      Ne.symm ab,Ne.symm ac,Ne.symm ad,Ne.symm bc,Ne.symm bd,Ne.symm cd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.pair_comm]
  · refine ⟨d,?_,?_⟩
    all_goals simp only [matching,anchor,opposites,dif_pos non,root]
    all_goals simp [Q,ab,ac,ad,bc,bd,cd,
      Ne.symm ab,Ne.symm ac,Ne.symm ad,Ne.symm bc,Ne.symm bd,Ne.symm cd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.pair_comm]
  · refine ⟨c,?_,?_⟩
    all_goals simp only [matching,anchor,opposites,dif_pos non,root]
    all_goals simp [Q,ab,ac,ad,bc,bd,cd,
      Ne.symm ab,Ne.symm ac,Ne.symm ad,Ne.symm bc,Ne.symm bd,Ne.symm cd,Finset.erase_insert_of_ne,Finset.erase_insert_eq_erase,Finset.pair_comm]

theorem pair_cover (U : Finset V) (R : Finset (Finset V)) (sub : R⊆edgeUniverse U)
    (P : Finset (Finset V)) (h : P∈R.powersetCard 2) :
    (∃ s∈stars U 2,star s=P) ∨
      ∃ Q∈U.powersetCard 4,∃ j∈opposites Q,matching Q j=P := by
  classical
  obtain ⟨inR,two⟩ := Finset.mem_powersetCard.mp h
  obtain ⟨e,f,ef,rfl⟩ := Finset.card_eq_two.mp two
  have ep := Finset.mem_powersetCard.mp (sub (inR (by simp : e∈({e,f}:Finset _))))
  have fp := Finset.mem_powersetCard.mp (sub (inR (by simp : f∈({e,f}:Finset _))))
  obtain ⟨a,b,ab,rfl⟩ := Finset.card_eq_two.mp ep.2
  obtain ⟨c,d,cd,rfl⟩ := Finset.card_eq_two.mp fp.2
  have ha := ep.1 (by simp : a∈({a,b}:Finset _))
  have hb := ep.1 (by simp : b∈({a,b}:Finset _))
  have hc := fp.1 (by simp : c∈({c,d}:Finset _))
  have hd := fp.1 (by simp : d∈({c,d}:Finset _))
  by_cases ac : a=c
  · subst c
    have bd : b≠d := fun h => ef (by rw [h])
    exact Or.inl (wedge_pair U a b d ab cd bd ha hb hd)
  by_cases ad : a=d
  · subst d
    have bc : b≠c := fun h => ef (by rw [h,Finset.pair_comm])
    left; simpa only [Finset.pair_comm c a] using wedge_pair U a b c ab ac bc ha hb hc
  by_cases bc : b=c
  · subst c
    left; simpa only [Finset.pair_comm b a] using wedge_pair U b a d ab.symm cd ad hb ha hd
  by_cases bd : b=d
  · subst d
    left; simpa only [Finset.pair_comm b a,Finset.pair_comm b c] using wedge_pair U b a c ab.symm bc ac hb ha hc
  exact Or.inr (disjoint_pair U a b c d ab ac ad bc bd cd ha hb hc hd)

end ThresholdUpperCatalogue
