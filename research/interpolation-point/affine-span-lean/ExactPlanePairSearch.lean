import ExactPlaneFirstRank
import ExactPlaneNumericalRows
import ExactPlaneEagerBank
namespace ExactPlanePairSearch
open ExactPlaneFirstRelation ExactPlanePhysicalConverse ExactPlaneResidualPivots
open ExactPlaneRelationPair
open scoped BigOperators
variable {r N d : Nat}
abbrev F := ZMod 2
abbrev Key (d : Nat) := Fin d→F

def combine (row : Fin r→Fin N→F) (x : Fin r→F) : Fin N→F := ∑ j,x j • row j

def pairs (row : Fin r→Fin N→F) :=
  let l := (ExactPlaneNumericalRows.words r).map (combine row)
  l.flatMap fun u=>l.map fun v=>(u,v)

theorem count (row : Fin r→Fin N→F) : (pairs row).length=4^r := by
  calc
    _ = (2^r)*(2^r) := by simp [pairs,List.length_flatMap,ExactPlaneNumericalRows.length_words,List.sum_replicate,Function.comp_def]
    _ = (2*2)^r := (mul_pow 2 2 r).symm
    _ = _ := rfl

theorem mem_pairs (row : Fin r→Fin N→F) (x y : Fin r→F) : (combine row x,combine row y)∈pairs row := by
  apply List.mem_flatMap.mpr
  refine ⟨_,List.mem_map.mpr ⟨x,ExactPlaneNumericalRows.mem_words x,rfl⟩,?_⟩
  exact List.mem_map.mpr ⟨_,List.mem_map.mpr ⟨y,ExactPlaneNumericalRows.mem_words y,rfl⟩,rfl⟩

abbrev WordPair (N : Nat) := (Fin N→F) × (Fin N→F)
def indices (w : WordPair N) := support w.1∪support w.2

def test (k : Fin N→Key d) (b h : Fin N→Plane) (w : WordPair N) : Bool :=
  decide (det (aggregate h w.1) (aggregate h w.2)≠0) &&
    ExactPlaneEagerBank.check ((indices w).sort (·≤·)) k b h

theorem test_iff (k : Fin N→Key d) (b h : Fin N→Plane) (w : WordPair N) :
    test k b h w=true ↔ Independent (aggregate h w.1) (aggregate h w.2) ∧ ExactTrace k b h (indices w) := by
  simp only [test,Bool.and_eq_true_iff,decide_eq_true_eq,det_ne_iff,ExactPlaneEagerBank.check_eq,
    ExactPlaneGaussianCandidate.check_iff,Finset.sort_toFinset]

def findPair (row : Fin r→Fin N→F) (k : Fin N→Key d) (b h : Fin N→Plane) :=
  (pairs row).find? (test k b h)

def solve (row : Fin r→Fin N→F) (k : Fin N→Key d) (b h : Fin N→Plane) :=
  (findPair row k b h).map indices

theorem returned {row : Fin r→Fin N→F} {k : Fin N→Key d} {b h : Fin N→Plane}
    {A : Finset (Fin N)} (ok : solve row k b h=some A) : ExactTrace k b h A := by
  unfold solve at ok
  cases e : findPair row k b h with
  | none => simp [e] at ok
  | some w =>
    have same : indices w=A := by simpa [e] using ok
    exact same ▸ ((test_iff _ _ _ _).mp (List.find?_some e)).2

theorem complete (row : Fin r→Fin N→F) (k : Fin N→Key d) (b h : Fin N→Plane)
    (covers : ∀ z∈first k b,∃ x,combine row x=z) :
    solve row k b h≠none ↔ ∃ A : Finset (Fin N),ExactTrace k b h A := by
  constructor
  · intro found
    cases e : solve row k b h with
    | none => exact False.elim (found e)
    | some A => exact ⟨A,returned e⟩
  · rintro ⟨A,tr⟩ no
    obtain ⟨g,u,v,mt,ru,rv,su,sv,ind⟩ := (exact_pair k b h A).mp tr
    obtain ⟨x,eqx⟩ := covers u ((le_iSup (relation k b) g) ru)
    obtain ⟨y,eqy⟩ := covers v ((le_iSup (relation k b) g) rv)
    have yes : test k b h (u,v)=true := by
      apply (test_iff _ _ _ _).mpr
      exact ⟨ind,pair_trace k b h _ g (fun i hi=>mt i ((Finset.union_subset su sv) hi))
        u v ru rv Finset.subset_union_left Finset.subset_union_right ind⟩
    have mem := mem_pairs row x y
    rw [eqx,eqy] at mem
    have e : findPair row k b h=none := Option.map_eq_none_iff.mp no
    exact (List.find?_eq_none.mp e (u,v) mem) yes

theorem basis_covers (k : Fin N→Key d) (b : Fin N→Plane)
    (B : Module.Basis (Fin r) F (first k b)) :
    ∀ z∈first k b,∃ x,combine (fun j=>(B j).val) x=z := by
  intro z hz
  let v : first k b := ⟨z,hz⟩
  refine ⟨fun j=>B.repr v j,?_⟩
  have eq := congrArg (fun w : first k b=>w.val) (B.sum_repr v)
  simpa only [combine,Submodule.coe_sum,Submodule.coe_smul] using eq

#print axioms count
#print axioms returned
#print axioms complete
end ExactPlanePairSearch
