import ThresholdStarEndpointRows
import ThresholdFactorCut
namespace ThresholdStarBypass
open PEqualNP.CircuitLowerBounds ThresholdOrGroups ThresholdOrExtraction T2OrPartition
open ThresholdRegularSource ThresholdSimpleIncidence

private theorem run_cat (u : Nat) (sel : Nat → Bool) (mode : Bool) (raw : Env)
    (pre post : List Block) (f : Env) :
    run u sel mode raw (pre++post) f=run u sel mode raw post (run u sel mode raw pre f) := by
  induction pre generalizing f with
  | nil => rfl
  | cons b pre ih => exact ih _

private theorem stable (u : Nat) (sel : Nat → Bool) (mode : Bool) (raw : Env)
    (bs : List Block) (f : Env) (j : Nat) (skip : ∀ b∈bs,b.out≠j) :
    run u sel mode raw bs f j=f j := by
  induction bs generalizing f with
  | nil => rfl
  | cons b bs ih =>
    change run _ _ _ _ bs _ j=f j
    rw [ih _ (fun a ha => skip a (by simp [ha]))]
    simp [put,Ne.symm (skip b (by simp))]

private theorem shield_by_split (u x v : Nat) (sel : Nat → Bool) (raw : Env) (bs : List Block) (f : Env)
    (loc : ∀ pre b post, bs=pre++b::post → Shield u x v (run u sel true raw pre f) b) :
    Shielded u x v sel raw bs f := by
  induction bs generalizing f with
  | nil => trivial
  | cons b bs ih =>
    exact ⟨loc [] b bs rfl,ih _ (fun pre a post eq => loc (b::pre) a post (by simp [eq]))⟩

/-- The remaining local premise names the pin opposite v of the actual
singleton reader z and its value in the completed baseline bypassed run.
All other exclusion and timing conditions follow from the checked forest. -/
theorem physical_shield {C : Circuit} {n : Nat} (L : Layout C n) (x : Fin n)
    (u v z : Id C) (pair : endpoints L x ⊆ {u,v})
    (only : readers C (n+v.val)=[z]) (andZ : (C.gates.get z).op=.and)
    (sel : Nat → Bool) (raw f : Env)
    (direct : ∀ l r, Block.meet (n+z.val) l r ∈ forest L Fin.val →
      (l=n+v.val ∧ r≠n+v.val ∧ run (n+u.val) sel true raw (forest L Fin.val) f r=false) ∨
      (r=n+v.val ∧ l≠n+v.val ∧ run (n+u.val) sel true raw (forest L Fin.val) f l=false))
    (receiver : ∃ l r, Block.meet (n+z.val) l r ∈ forest L Fin.val) :
    Shielded (n+u.val) x.val (n+v.val) sel raw (forest L Fin.val) f ∧
      ∀ b∈forest L Fin.val, OutsideTaps (n+u.val) (n+v.val) sel b := by
  let bs := forest L Fin.val
  have ordered := forest_ordered L Fin.val
  obtain ⟨lz,rz,hz⟩ := receiver
  have distinguish (b : Block) (hb : b∈bs) (hzWire : b.out=n+z.val) :
      b=.meet (n+z.val) lz rz := by
    have nd := ThresholdFactorCut.output_nodup L Fin.val
    exact List.inj_on_of_nodup_map nd hb hz hzWire
  constructor
  · apply shield_by_split
    intro pre b post split
    have mem : b∈bs := by dsimp [bs]; rw [split]; simp
    by_cases isV : b.out=n+v.val
    · exact Or.inr (Or.inl isV)
    have free := raw_free_off_pair L x u v pair b mem isV
    by_cases spectator : b.out≠n+z.val
    · have dst := ThresholdFactorCut.physical_no_other L Fin.val z andZ only b mem spectator
      rcases free with force|free
      · exact Or.inl force
      · apply Or.inr; apply Or.inr
        cases b with
        | group p t => exact ⟨free,dst⟩
        | meet w l r => exact Or.inl ⟨fun e => dst (by simp [Block.exts,e]),fun e => dst (by simp [Block.exts,e])⟩
    have bz := distinguish b mem (by simpa using spectator)
    subst b
    have shape := forest_checked L Fin.val _ hz
    change GateAt C n (n+z.val) .and lz rz at shape
    have before (j : Nat) (lt : j<n+z.val) :
        run (n+u.val) sel true raw bs f j=run (n+u.val) sel true raw pre f j := by
      change run _ _ _ _ (forest L Fin.val) _ _=_
      rw [split,run_cat]
      apply stable
      intro a ha
      rcases List.mem_cons.mp ha with rfl|h
      · exact Ne.symm (Nat.ne_of_lt lt)
      · have order := ordered
        rw [split,List.pairwise_append] at order
        have later := (List.pairwise_cons.mp order.2.1).1 a h
        change n+z.val<a.out at later
        omega
    rcases direct lz rz hz with ⟨l,r,off⟩|⟨r,l,off⟩
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨l,r,(before rz shape.rightEarlier).symm.trans off⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨r,l,(before lz shape.leftEarlier).symm.trans off⟩)))
  · intro b hb
    cases b with
    | meet => trivial
    | group p t =>
      intro _ _
      apply ThresholdFactorCut.physical_no_other L Fin.val z andZ only (.group p t) hb
      intro e
      have impossible := distinguish _ hb e
      contradiction
#print axioms physical_shield
end ThresholdStarBypass
