import SixD3OriginalFamilies9822
import SixD3ArmsProjection9822
import SixD3OriginalEnvironment9822
namespace Research.Graph9822Profiles.OuterLive
open Research.Graph9822Resolution Research.Graph9822 Research.Graph9822.ArbitraryScan Research.Graph9822Profiles.Fresh
open Research.SixD3.Labels Research.Graph9822.ThreeDirect
open PEqualNP.Outside.L_meta_9822.Sectors
noncomputable section
local instance (p : Prop) : Decidable p := Classical.propDecidable p
theorem original_d3_projection (gs : List DGate) (out : Nat) (size : gs.length≤17)
    (ok : WellWired gs 10) (ob : out<10+gs.length) (six : gs.countP Gate.isAnd=6)
    (computes : ∀ x : Fin 10 → Bool,(asCircuit gs out).eval (List.ofFn x)=edge x) :
    let axis := switchAxis (switchAddrs gs 10) ((switchAddrs_length gs 10).trans_le six.le)
    let st := (gateEvents axis gs 10 ++ rawEvents 10).foldl paddedStep (initial out)
    let R := tenR axis gs out
    let P := field st.switches
    ((Finset.univ : Finset (Fin 10)).filter (fun v=>RayValue P (R v))).card=3 →
    ∃ d∈roster38, Nonempty (Rooms d false) ∨ Nonempty (Shared d) := by
  classical
  intro axis st R P three
  obtain ⟨real,anti,edges,stable,pos⟩ := original_d3_environment gs out size ok ob six computes
  obtain ⟨r⟩ := choose_three three real
  obtain ⟨N,e,one,defN,names,fam⟩ := original_d3_families gs out size ok ob six computes three
  have raw (v) (nd : ¬RayValue P (R v)) := (defN (R v)).2 ⟨v,rfl,nd⟩
  rcases fam with plain|⟨H,hm,a,c,_,_,ac,he,fixed,m,hm',sub,_⟩
  · obtain ⟨arms⟩ := ordinary_arms r (fun v nd=>plain _ (raw v nd))
    obtain ⟨keep,sel,opp⟩ := select_physical arms real edges
    exact ⟨_,keep,Or.inl (ordinary_projection r.roots P R _ arms.L real arms.meaning sel opp)⟩
  · obtain ⟨arms⟩ := mixed_arms r a c ac (fun v nd=>fixed _ (raw v nd))
    obtain ⟨v,rv,nd⟩ := (defN m).1 hm'
    change R v=m at rv
    change ¬RayValue P m at nd
    have issued (i) : Primitive P (P i) ∨ (∃u,R u=P i) ∨ P i=H := by
      rcases names i with prim|n|exc
      · exact Or.inl prim
      · obtain ⟨u,eq,_⟩ := (defN _).1 n
        exact Or.inr (Or.inl ⟨u,eq⟩)
      · cases e with
        | nil => simp at exc
        | cons f tail =>
          have empty : tail=[] := List.length_eq_zero_iff.mp (by simp only [List.length_cons] at one; omega)
          subst tail
          exact Or.inr (Or.inr ((List.mem_singleton.mp exc).trans (List.mem_singleton.mp hm).symm))
    obtain ⟨keep,A⟩ := project_mixed r a c ac arms real edges anti stable pos H he
      ⟨v,rv.symm ▸ nd,rv.symm ▸ sub⟩ issued
    exact ⟨_,keep,Or.inr A⟩
end
end Research.Graph9822Profiles.OuterLive
#print axioms Research.Graph9822Profiles.OuterLive.original_d3_projection
