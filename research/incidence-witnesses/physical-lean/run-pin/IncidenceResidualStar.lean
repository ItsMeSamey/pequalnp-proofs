import Research.CircuitRewire
namespace IncidenceResidualStar
open CircuitRewire

/-- Flipping the once-read raw must sensitize its meet.  The other operand
therefore accepts the neighboring singleton before the raw is activated. -/
theorem star {Z : Type*} (n s out x j v : ℕ) (g : ℕ → Gate) (X : ℕ → Set Z)
    (on off : Z) (hx : x<n) (hj : j<s) (hout : out<n+s) (internal : out≠x)
    (ord : ∀ t<s,(g t).left<n+t ∧ (g t).right<n+t)
    (sem : ∀ t<s,X (n+t)=(g t).eval X)
    (kind : (g j).op=.meet)
    (ports : ((g j).left=x ∧ (g j).right=v) ∨ ((g j).right=x ∧ (g j).left=v))
    (other : v≠x)
    (only : ∀ t<s,t≠j → (g t).left≠x ∧ (g t).right≠x)
    (raw : ∀ i<n,i≠x → (on∈X i ↔ off∈X i))
    (pos : on∈X out) (neg : off∉X out) : off∈X v := by
  by_contra cold
  have same (i : ℕ) : i<n+s → i≠x → (on∈X i ↔ off∈X i) := by
    induction i using Nat.strong_induction_on with
    | ind i ih =>
      intro valid ne
      by_cases lo : i<n
      · exact raw i lo ne
      let t := i-n
      have form : i=n+t := by dsimp [t]; omega
      have ht : t<s := by omega
      obtain ⟨hl,hr⟩ := ord t ht
      rw [form,sem t ht]
      by_cases eq : t=j
      · subst j
        have before : v<i := ports.elim (fun p => p.2 ▸ (show (g t).right<i by omega))
          (fun p => p.2 ▸ (show (g t).left<i by omega))
        have offOn : on∉X v := fun h => cold ((ih v before (by omega) other).mp h)
        rcases ports with ⟨l,r⟩|⟨r,l⟩ <;> simp [Gate.eval,kind,Op.eval,r,l,cold,offOn]
      · have ⟨nl,nr⟩ := only t ht eq
        have l := ih (g t).left (by omega) (by omega) nl
        have r := ih (g t).right (by omega) (by omega) nr
        cases op : (g t).op <;> simp only [Gate.eval,op,Op.eval,Set.mem_union,Set.mem_inter_iff] <;> tauto
  exact neg ((same out hout internal).mp pos)
#print axioms star
end IncidenceResidualStar
