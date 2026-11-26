import ThresholdActualFineLoss
import ThresholdFamilySimpleGraph
namespace ThresholdAmbientEffectiveGraph
variable {I V : Type*} [DecidableEq I] [DecidableEq V] [Fintype V]
variable (R : Finset I) (col : I → Finset V)
def fullGraph : SimpleGraph V where
  Adj a b := a≠b ∧ {a,b}∈R.image col
  symm := ⟨fun a b h=>⟨h.1.symm,by simpa [Finset.pair_comm] using h.2⟩⟩
  loopless := ⟨fun v h=>h.1 rfl⟩
instance : DecidableRel (fullGraph R col).Adj :=
  fun a b => inferInstanceAs (Decidable (a≠b ∧ {a,b}∈R.image col))
def support := R.biUnion col
abbrev activeGraph := ThresholdFamilySimpleGraph.graph (support R col) (R.image col)
instance : DecidableRel (activeGraph R col).Adj := fun a b =>
  inferInstanceAs (Decidable (a≠b ∧ {a.val,b.val}∈R.image col))

theorem both {a b : V} (h : (fullGraph R col).Adj a b) :
    a∈support R col ∧ b∈support R col := by
  obtain ⟨r,hr,eq⟩ := Finset.mem_image.mp h.2
  exact ⟨Finset.mem_biUnion.mpr ⟨r,hr,by simp [eq]⟩,Finset.mem_biUnion.mpr ⟨r,hr,by simp [eq]⟩⟩

theorem degree_on (a : ↥(support R col)) :
    (activeGraph R col).degree a=(fullGraph R col).degree a.val := by
  classical
  have same : ((activeGraph R col).neighborFinset a).map (Function.Embedding.subtype _)=
      (fullGraph R col).neighborFinset a.val := by
    ext v
    constructor
    · intro hv
      obtain ⟨b,nb,rfl⟩ := Finset.mem_map.mp hv
      have ab := ((activeGraph R col).mem_neighborFinset a b).mp nb
      exact ((fullGraph R col).mem_neighborFinset _ _).mpr ⟨fun eq=>ab.1 (Subtype.ext eq),ab.2⟩
    · intro hv
      have ab := ((fullGraph R col).mem_neighborFinset _ _).mp hv
      let b : ↥(support R col) := ⟨v,(both R col ab).2⟩
      exact Finset.mem_map.mpr ⟨b,((activeGraph R col).mem_neighborFinset _ _).mpr
        ⟨fun eq=>ab.1 (congrArg Subtype.val eq),ab.2⟩,rfl⟩
  simpa using congrArg Finset.card same
theorem degree_off {a : V} (off : a∉support R col) : (fullGraph R col).degree a=0 := by
  classical
  have empty : (fullGraph R col).neighborFinset a=∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro b hb
    exact off (both R col (((fullGraph R col).mem_neighborFinset _ _).mp hb)).1
  simpa using congrArg Finset.card empty

theorem degree_square : (∑ v : V,(fullGraph R col).degree v^2)=
    ∑ v : ↥(support R col),(activeGraph R col).degree v^2 := by
  classical
  let S := support R col
  let f := fun v : V=>(fullGraph R col).degree v^2
  have narrow : (∑ v : V,f v)=∑ v∈S,f v :=
    (Finset.sum_subset (Finset.subset_univ S) (fun v _ off=>by simp [f,degree_off R col off])).symm
  change (∑ v : V,f v)=_
  rw [narrow]
  have eq := (Finset.sum_attach S f).symm
  rw [Finset.attach_eq_univ] at eq
  rw [eq]
  apply Finset.sum_congr rfl
  intro v _
  exact congrArg (fun x : Nat => x^2) (degree_on R col v).symm

theorem width : Fintype.card ↥(support R col)=(R.biUnion col).card := Fintype.card_coe _

noncomputable def edge (fallback : V) (r : I) : Sym2 V := by
  classical
  exact if h : ∃ a b : V,a≠b ∧ col r={a,b} then Sym2.mk h.choose h.choose_spec.choose
    else Sym2.mk fallback fallback

private theorem pair {a b : V} (ne : a≠b) {r : I} (eq : col r={a,b}) (fallback : V) :
    edge col fallback r=Sym2.mk a b := by
  classical
  let h : ∃ c d : V,c≠d ∧ col r={c,d} := ⟨a,b,ne,eq⟩
  have same := h.choose_spec.choose_spec.2.symm.trans eq
  apply Sym2.ext
  intro v
  simp only [edge,dif_pos h,Sym2.mem_iff]
  simpa [Finset.mem_insert,Finset.mem_singleton] using
    (congrArg (fun p : Finset V=> v∈p) same).to_iff

theorem edge_suite (fallback : V) (two : ∀ r∈R,(col r).card=2) (inj : Set.InjOn col (R:Set I)) :
    Set.InjOn (edge col fallback) (R:Set I) ∧
    (∀ r∈R,∀ v∈col r,edge col fallback r∈(fullGraph R col).incidenceFinset v) ∧
    (∀ r∈R,∀ a b,col r={a,b} → (fullGraph R col).Adj a b) := by
  classical
  have aa r (hr : r∈R) a b (eq : col r={a,b}) : (fullGraph R col).Adj a b := by
    refine ⟨?_,Finset.mem_image.mpr ⟨r,hr,eq⟩⟩
    intro e; subst b; have bad := two r hr; simp [eq] at bad
  constructor
  · intro r hr s hs es
    apply inj hr hs
    obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp (two r hr)
    obtain ⟨c,d,cd,eq'⟩ := Finset.card_eq_two.mp (two s hs)
    rw [pair col ab eq fallback,pair col cd eq' fallback] at es
    simpa [eq,eq',Sym2.toFinset_mk_eq] using congrArg Sym2.toFinset es
  refine ⟨?_,aa⟩
  intro r hr v hv
  obtain ⟨a,b,ab,eq⟩ := Finset.card_eq_two.mp (two r hr)
  rw [pair col ab eq fallback]
  have gr := aa r hr a b eq
  rw [SimpleGraph.mem_incidenceFinset]
  refine ⟨gr,?_⟩
  simpa [eq] using hv
end ThresholdAmbientEffectiveGraph
