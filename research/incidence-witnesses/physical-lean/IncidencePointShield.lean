import IncidenceStartNormalization
namespace IncidencePointShield
open CircuitRewire SparseIncidence IncidenceStartNormalization

/-- Reachability from one raw in the physical directed graph after blocking one wire. -/
def shadow (m : Nat) (code : Nat→Gate) (x cut : Nat) : Nat→Nat→Bool
  | 0 => fun i=>decide (i=x ∧ i≠cut)
  | a+1 =>
    let old := shadow m code x cut a
    put old (m+a) (decide (m+a≠cut) && (old (code a).left || old (code a).right))

theorem old (m : Nat) (code : Nat→Gate) (x cut a s j : Nat) (le : a≤s) (lt : j<m+a) :
    shadow m code x cut s j=shadow m code x cut a j := by
  induction s,le using Nat.le_induction with
  | base => rfl
  | succ k hk ih => simp [shadow,put,show j≠m+k by omega,ih]

theorem raw (m s : Nat) (code : Nat→Gate) (x cut j : Nat) (lt : j<m) :
    shadow m code x cut s j=decide (j=x ∧ j≠cut) :=
  old _ _ _ _ 0 _ _ (by omega) (by omega)

theorem gate (m s : Nat) (code : Nat→Gate) (x cut a : Nat) (lt : a<s)
    (l : (code a).left<m+a) (r : (code a).right<m+a) :
    shadow m code x cut s (m+a)=
    (decide (m+a≠cut) && (shadow m code x cut s (code a).left ||
      shadow m code x cut s (code a).right)) := by
  rw [old m code x cut (a+1) s _ (by omega) (by omega)]
  simp only [shadow,put,ite_true,old m code x cut a s _ (by omega) l,
    old m code x cut a s _ (by omega) r]

theorem shield {Z : Type*} (m s : Nat) (code : Nat→Gate) (X : Nat→Set Z)
    (ord : ∀ a<s,(code a).left<m+a ∧ (code a).right<m+a)
    (sem : ∀ a<s,X (m+a)=(code a).eval X) (x cut : Nat) (u v : Z)
    (inputs : ∀ i<m,i≠x → (u∈X i ↔ v∈X i)) (same : u∈X cut ↔ v∈X cut)
    (j : Nat) (bound : j<m+s) (blocked : shadow m code x cut s j=false) :
    u∈X j ↔ v∈X j := by
  induction j using Nat.strong_induction_on with
  | ind j ih =>
    by_cases stop : j=cut
    · simpa [stop] using same
    by_cases src : j<m
    · apply inputs j src
      intro eq
      rw [raw m s code x cut j src] at blocked
      simp [eq,show x≠cut from eq ▸ stop] at blocked
    let a := j-m
    have idx : j=m+a := by dsimp [a]; omega
    have aa : a<s := by omega
    obtain ⟨l,r⟩ := ord a aa
    rw [idx,gate m s code x cut a aa l r] at blocked
    have notcut : m+a≠cut := idx ▸ stop
    simp [notcut] at blocked
    have left := ih (code a).left (by omega) (by omega) blocked.1
    have right := ih (code a).right (by omega) (by omega) blocked.2
    rw [idx,sem a aa]
    cases h : (code a).op <;> simp [Gate.eval,Op.eval,h,left,right]

/-- If the selected point changes the output and every path goes through the cut, the cut
also changes. Its value on the smaller assignment must be false by monotonicity. -/
theorem low_at_cut {Z : Type*} (m s : Nat) (code : Nat→Gate) (X : Nat→Set Z)
    (ord : ∀ a<s,(code a).left<m+a ∧ (code a).right<m+a)
    (sem : ∀ a<s,X (m+a)=(code a).eval X) (x cut out : Nat) (u v : Z)
    (inputs : ∀ i<m,i≠x → (u∈X i ↔ v∈X i)) (mono : u∈X cut → v∈X cut)
    (endIndex : out<m+s) (paths : shadow m code x cut s out=false)
    (no : u∉X out) (yes : v∈X out) : u∉X cut := by
  intro on
  exact no ((shield m s code X ord sem x cut u v inputs ⟨fun _=>mono on,fun _=>on⟩
    out endIndex paths).mpr yes)
#print axioms low_at_cut
end IncidencePointShield
