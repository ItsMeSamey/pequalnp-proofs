import ExactPlaneGeneratedDecision
namespace ExactPlaneProfileCharts
open ExactPlaneSuppliedCoordinates ExactPlanePhysicalConverse ExactPlaneResidualPivots ExactPlaneObservedSpan
open ExactPlaneFieldSampler (V)
variable {N d : ℕ}

abbrev X (d : ℕ) := V (d+d)

noncomputable def chart (x : X d) : Key d →ₗ[ZMod 2] Plane :=
  (ExactPlaneGlobalSeed.equiv (Pi.basisFun (ZMod 2) (Fin d))).symm (ExactPlaneGeneratedDecision.coordinate x)

noncomputable def onObserved (priv : Fin N→Key d) (x : X d) : observed priv →ₗ[ZMod 2] Plane :=
  (chart x).comp (observed priv).subtype

theorem onto (priv : Fin N→Key d) : Function.Surjective (onObserved priv) := by
  intro g
  obtain ⟨G,hG⟩ := g.exists_extend
  obtain ⟨x,hx⟩ := ExactPlaneGeneratedDecision.onto d
    (ExactPlaneGlobalSeed.equiv (Pi.basisFun (ZMod 2) (Fin d)) G)
  change ExactPlaneGeneratedDecision.coordinate x=_ at hx
  refine ⟨x,?_⟩
  unfold onObserved chart
  rw [hx,LinearEquiv.symm_apply_apply]
  exact hG

def table (priv : Fin N→Key d) (x : X d) : Fin N→Plane :=
  fun i => value (ExactPlaneGeneratedDecision.coordinate x) (priv i)

theorem table_chart (priv : Fin N→Key d) (x : X d) (i : Fin N) :
    table priv x i=onObserved priv x (key priv i) :=
  value_chart _ _

def active (priv : Fin N→Key d) (tag : Fin N→Plane) (x : X d) :=
  ExactPlaneExecutableSelector.accept (fun (q : Fin N→Plane) i=>q i) tag (table priv x)

theorem mem_active (priv : Fin N→Key d) (tag : Fin N→Plane) (x : X d) (i : Fin N) :
    i∈active priv tag x ↔ onObserved priv x (key priv i)=tag i := by
  simp [active,ExactPlaneExecutableSelector.accept,table_chart,eq_comm]

noncomputable def read (p : Key d) : X d →ₗ[ZMod 2] Plane :=
  (LinearMap.applyₗ (R:=ZMod 2) p).comp
    ((ExactPlaneGlobalSeed.equiv (Pi.basisFun (ZMod 2) (Fin d))).symm.toLinearMap.comp
      (ExactPlaneGeneratedDecision.chartMap d))

theorem read_apply (p : Key d) (x : X d) : read p x = chart x p := rfl
end ExactPlaneProfileCharts
