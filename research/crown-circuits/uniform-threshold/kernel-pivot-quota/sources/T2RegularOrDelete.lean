import T2RegularShape
import T2SoleAndCase
import T2RawUsed
import T2DoubleReader
import T2SoleOrCaller
import T2BenchmarkNormalize

namespace T2RegularOrDelete
open PEqualNP.CircuitLowerBounds ResidualSurplus T2PhysicalOverride T2CubeDeletion
open T2SoleOrSplice T2SoleAndMinor T2RawTopology T2DoubleReader

def Saving (m size : Nat) : Prop :=
  ∃ D : Circuit, PEqualNP.MetaComplexity.Monotone2 D ∧ Computes m D ∧ D.size+3≤size

theorem decode (gs : List Gate) (k : Nat) (h : SuffixOK k gs) :
    ∃ rs : List Raw, rs.map native=gs ∧ RawValid k rs := by
  induction gs generalizing k with
  | nil => exact ⟨[],rfl,True.intro⟩
  | cons g gs ih =>
    obtain ⟨⟨o,x,y,rfl,hx,hy⟩,tail⟩ := h
    obtain ⟨rs,eq,v⟩ := ih (k+1) tail
    exact ⟨(o,x,y)::rs,by simp [native,eq],hx,hy,v⟩

theorem no_dup {n out : Nat} {gs : List Raw} (v : RawValid n gs)
    (lc : LexMinimum n (source gs out)) :
    ∀ r ∈ gs, r.2.1 ≠ r.2.2 := by
  rintro ⟨o,x,y⟩ mem e
  change x=y at e
  subst y
  obtain ⟨a,b,rfl⟩ := List.append_of_mem mem
  exact no_duplicate_raw n x out a b o (valid_tail a _ n v).1 lc

theorem one_impossible {m out : Nat} (two : 2≤m) (i : Fin (m+1)) (gs : List Raw)
    (v : RawValid (m+1) gs) (lc : LexMinimum (m+1) (source gs out))
    (no : ¬ Saving m gs.length) : (gs.filter (rawReads i.val)).length ≠ 1 := by
  intro len
  obtain ⟨a,⟨o,x,y⟩,b,rfl,hx,le,ri⟩ := one_position len
  have nd : x ≠ y := no_dup v lc (o,x,y) (by simp)
  have rwrow : x=i.val ∨ y=i.val := read_iff.mp hx
  have obs : out < (m+1)+(a++(o,x,y)::b).length := by
    simpa [source] using lc.eligible.2.1
  cases o with
  | and =>
    apply no
    rcases rwrow with rfl | rfl
    · exact sole_and_case two i out y _ _ a b (Or.inl ⟨rfl,rfl⟩) nd.symm le ri v obs lc.eligible.1
    · exact sole_and_case two i out x _ _ a b (Or.inr ⟨rfl,rfl⟩) nd le ri v obs lc.eligible.1
  | or =>
    obtain ⟨p,swap,eq⟩ : ∃ p : Nat, ∃ swap : Bool,
        source (a++(.or,x,y)::b) out = original swap (a.map native) (b.map native) i.val p out := by
      rcases rwrow with rfl | rfl
      · exact ⟨y,false,by simp [source_eq,original,reader,native]⟩
      · exact ⟨x,true,by simp [source_eq,original,reader,native]⟩
    rw [eq] at lc
    exact no_sole_reader _ i p out _ _ swap lc.eligible lc.primary lc.secondary le ri

theorem classify {m out : Nat} (two : 2≤m) (gs : List Raw) (v : RawValid (m+1) gs)
    (lc : LexMinimum (m+1) (source gs out)) : Saving m gs.length ∨ Regular (m+1) gs := by
  classical
  by_cases no : Saving m gs.length
  · exact Or.inl no
  right
  refine ⟨?_,no_dup v lc⟩
  intro i
  have pos := T2RawUsed.positive_readers (by omega : 2≤m+1) gs lc.eligible i
  have neverOne := one_impossible two i gs v lc no
  have small : (gs.filter (rawReads i.val)).length ≤ 2 := by
    by_contra! largeCount
    have len : (tags false i).length = m+1 := by simp [tags_len]
    have valid : Valid (tags false i).length (annotate gs (tags false i)) := by
      rw [annotate_valid_iff,len]; exact v
    have obs : out<(tags false i).length+(annotate gs (tags false i)).length := by
      simpa [len,annotate_len,source] using lc.eligible.2.1
    obtain ⟨D,mono,rep,cost⟩ := direct_deletion false i gs out two
      (correct_on_plain i gs out lc.eligible.1) valid obs
    apply no
    refine ⟨D,mono,rep,?_⟩
    simp only [pinnedIndex,Bool.false_eq_true,if_false,Nat.zero_add] at cost
    omega
  have num : (gs.filter (rawReads i.val)).length=2 := by omega
  refine ⟨num,?_⟩
  obtain ⟨a,r,b,s,c,shape,yr,ys,lookup⟩ := two_positions num
  let j := a.length
  let k := (a ++ r::b).length
  have ij : j≠k := by simp [j,k]
  have atR : At gs j r := ⟨a,b++s::c,shape,rfl⟩
  have atS : At gs k s := ⟨a++r::b,c,by simpa [List.append_assoc] using shape,rfl⟩
  have rr : Reads r i.val := read_iff.mp yr
  have sr : Reads s i.val := read_iff.mp ys
  have ro : r.1=.or := by
    cases e : r.1 with
    | or => rfl
    | and => exact False.elim (no (double_and_deletion i gs out j k r s two lc atR e rr atS sr ij))
  have so : s.1=.or := by
    cases e : s.1 with
    | or => rfl
    | and => exact False.elim (no (double_and_deletion i gs out k j s r two lc atS e sr atR rr ij.symm))
  intro t ht read
  rcases lookup t ht read with rfl | rfl
  · exact ro
  · exact so

theorem regular_or_delete {m : Nat} (two : 2≤m) (C : Circuit)
    (mono : PEqualNP.MetaComplexity.Monotone2 C) (rep : Computes (m+1) C) :
    Saving m C.size ∨ ∃ gs : List Raw, ∃ out : Nat,
      LexMinimum (m+1) (source gs out) ∧ gs.length≤C.size ∧ Regular (m+1) gs := by
  obtain ⟨E,eligible,budget⟩ := T2BenchmarkNormalize.canNormalize (by omega : 2≤m+1) C mono rep
  obtain ⟨F,lc⟩ := exists_lexMinimum (n:=m+1) ⟨E,eligible⟩
  have floor := (lc.primary E eligible).trans budget
  obtain ⟨gs,e,v⟩ := decode F.gates (m+1) ((eligible_iff _ _).mp lc.eligible).2.2
  have orig : source gs F.output = F := by
    rw [source_eq,e]
  have sz : gs.length≤C.size := by
    have eq := congrArg List.length e
    simp only [List.length_map] at eq
    change F.gates.length ≤ C.size at floor
    omega
  have L : LexMinimum (m+1) (source gs F.output) := orig.symm ▸ lc
  rcases classify two gs v L with save | regular
  · obtain ⟨D,hm,hc,cost⟩ := save
    exact Or.inl ⟨D,hm,hc,cost.trans sz⟩
  · exact Or.inr ⟨gs,F.output,L,sz,regular⟩

#print axioms regular_or_delete
end T2RegularOrDelete
