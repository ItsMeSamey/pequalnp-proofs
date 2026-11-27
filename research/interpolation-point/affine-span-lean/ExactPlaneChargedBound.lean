import ExactPlaneChargedSolver
namespace ExactPlaneChargedSolver
open ExactPlaneSuppliedCoordinates (Key)
open ExactPlaneChargedSites (Table)
variable {N d : Nat}

/-- One unit for each labelled action, two units for each tag-pair comparison
slot. Row arithmetic, list allocation and runtime are outside this measure. -/
def charges (z : Output N) :=
  z.deficit.scan.keyBits+2*z.deficit.scan.tagPairs+z.deficit.visits+
  z.field.modulusCandidates+z.field.divisions+z.field.fieldMuls+z.field.dotEntries+
  z.field.baseTables+z.field.seedRows+z.emitted+z.terms+
  z.search.tested+z.search.siteTests+z.search.checkPivots+z.search.recovered+z.search.basisPivots

def upper (N d t : Nat) :=
  let m := d+d
  let R := budget t
  let q := ExactPlaneChargedGenerator.q m R
  let e := ExactPlaneConstructedRows.exponent m R
  let s := seedSize m R
  let C := ExactPlaneChargedOdd.card s
  N^2*(d+8)+4*N*(d+4)+q+q*(2^(e/2+1)-2)+q*m+q^2*m+q+s+C+ExactPlaneChargedOdd.occurrences s+
    C+C*N+C*((N+5)*(d+4))+1+2*N*(d+4)

theorem charge_bound (p : Fin N→Key d) (b h : Table N) :
    charges (run p b h)≤upper N d (ExactPlaneComputedDeficit.computed p b) := by
  let z := run p b h
  obtain ⟨t,_,_,pre,_,_,vis⟩ := preprocess p b h
  obtain ⟨mc,dv,mul,dots,tables,s⟩ := field p b h
  obtain ⟨em,occ⟩ := enumeration p b h
  obtain ⟨tr,sites,ch,rec,bs⟩ := traversal p b h
  have recovery : z.search.recovered≤1 := by rw [rec]; split <;> omega
  have divs := dv.trans (Nat.mul_le_mul_right _ mc)
  have checks := ch.trans (Nat.mul_le_mul_right _ tr)
  have tests := sites.le.trans (Nat.mul_le_mul_right _ tr)
  have bases := bs.trans (Nat.mul_le_mul_right _ recovery)
  simp only [Nat.one_mul] at bases
  unfold charges upper
  dsimp only
  rw [←t,←s,←em]
  replace em : (run p b h).emitted ≤ (run p b h).emitted := le_rfl
  replace s : (run p b h).field.seedRows ≤ (run p b h).field.seedRows := le_rfl
  apply Nat.add_le_add _ bases
  apply Nat.add_le_add _ recovery
  apply Nat.add_le_add _ checks
  apply Nat.add_le_add _ tests
  apply Nat.add_le_add _ tr
  apply Nat.add_le_add _ occ.le
  apply Nat.add_le_add _ em
  apply Nat.add_le_add _ s
  apply Nat.add_le_add _ tables.le
  apply Nat.add_le_add _ dots.le
  apply Nat.add_le_add _ mul.le
  apply Nat.add_le_add _ divs
  apply Nat.add_le_add _ mc
  apply Nat.add_le_add _ vis
  exact pre

theorem no_recovery {p : Fin N→Key d} {b h : Table N}
    (noneFound : ExactPlaneDeficitSolver.solve p b h=none) :
    (run p b h).search.recovered=0 ∧ (run p b h).search.basisPivots=0 := by
  obtain ⟨_,_,_,rec,bas⟩ := traversal p b h
  rw [answer,noneFound] at rec
  simp only [Option.isSome_none,Bool.false_eq_true,ite_false] at rec
  exact ⟨rec,by simpa [rec] using bas⟩

#print axioms charge_bound
#print axioms no_recovery
end ExactPlaneChargedSolver
