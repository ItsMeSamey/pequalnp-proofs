import IncidencePinRunTests
import IncidencePinRunRoom
import IncidencePinRunModel
namespace IncidencePinRunBound
open SparseIncidence CircuitRewire IncidenceStartNormalization IncidenceHoistReaders IncidenceHoistWalk
open IncidenceHoistPrefix IncidenceHoistSparse IncidenceHoistPrune IncidencePinPlaneGeometry
open IncidencePinFreeSites
variable {n : Nat} (C : Circuit n) (I : Fin n→Fin n→Prop) [DecidableRel I]

theorem bound (bin : binary C) (live : Live C) (andL : soleAnd C n)
    (neg : negatives C I n 2) (pos : flags C I)
    (degree : ∀ l,Fintype.card {p // I p l}=402)
    (unique : ∀ a b,a≠b → ∃! l,I a l ∧ I b l) (hn : n=161203)
    (P : Finset (Fin n)) (l : Fin n) (nonempty : P.Nonempty) (on : ∀ p∈P,I p l)
    (small : P.card≤400) :
    4*n-1-(2*(2*n-(402*P.card+1)))/(402-P.card+1)-P.card+
      (IncidencePhysicalPinExpectation.forced C P).card ≤ C.size := by
  let Q := removedLines I P
  have plane : n=401^2+401+1 := by omega
  have cardQ : Q.card=1+401*P.card := collinear_card I degree unique (by decide : 0<401) plane P l nonempty on
  have free : Q.card<n := by omega
  obtain ⟨hasPoint,hasLine,available,survives⟩ :=
    IncidencePinRunRoom.existence I degree unique (by decide : 0<401) plane P (by omega) free
  obtain ⟨D,bD,liveD,room,lo,hi⟩ :=
    IncidencePinRunRoom.room C I bin live andL neg pos P Q hasPoint hasLine available survives
  have count := total P Q
  have hm : 0<m P Q := by omega
  have removed (p) (hp : p∈P) (j) (inc : I p j) : j∈Q := (removed_iff I P j).mpr ⟨p,hp,inc⟩
  have lower := IncidencePinRunModel.lower D (raw P Q hm) bD liveD (neighbors I P Q)
    (by omega : 1<402-P.card) (min_degree I degree unique (by decide : 0<401) plane P)
    (fun x r h => overlap I unique P Q x r h.symm)
    (IncidencePinRunTests.singleton I C D P Q hm pos neg removed lo hi)
    (IncidencePinRunTests.pair I C D P Q hm pos neg removed lo hi)
  have eq : m P Q=2*n-(402*P.card+1) := by omega
  rw [eq] at lower
  have denom : 0<402-P.card+1 := by omega
  have frac := Nat.div_le_self (2*(2*n-(402*P.card+1))) (402-P.card+1)
  omega

#print axioms bound
end IncidencePinRunBound
