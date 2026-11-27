import DoubleIncidence

namespace PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual

inductive Root where
  | arm (side : Fin 2)
  | ext (top : ℕ)
  deriving DecidableEq

inductive Node where
  | row (original : ℕ)
  | arm (side : Fin 2)
  deriving DecidableEq

def Root.node : Root → Node
  | .arm b => .arm b
  | .ext j => .row j

theorem Root.node_injective : Function.Injective Root.node := by
  intro a b h
  cases a <;> cases b <;> simp_all [Root.node]

/-- Pins identify retained producers after following bypasses. None denotes a primary
input or symbolic true. An unaffected top is a retained original row, so its AND reader
is counted exactly once. The replacement arm roots are fresh gates. -/
structure DAG where
  paidRows : Finset ℕ
  extTops : Finset ℕ
  pins : ℕ → Fin 2 → Option ℕ
  armPins : Fin 2 → Fin 2 → Option ℕ

namespace DAG

def roots (D : DAG) : Finset Root :=
  (Finset.univ.image Root.arm) ∪ (D.extTops.image Root.ext)

def readers (D : DAG) (g : ℕ) : Finset Node :=
  ((D.paidRows.filter (fun j => ∃ b : Fin 2, D.pins j b = some g)).image Node.row) ∪
  ((Finset.univ.filter (fun a : Fin 2 => ∃ b : Fin 2, D.armPins a b = some g)).image Node.arm)

def step (D : DAG) : Node → Node → Prop
  | .row g, v => g ∈ D.paidRows ∧ g ∉ D.extTops ∧ v ∈ D.readers g
  | .arm _, _ => False

noncomputable def reaches (D : DAG) (g : ℕ) : Finset Root := by
  classical
  exact D.roots.filter (fun r => Relation.ReflTransGen D.step (.row g) r.node)

theorem mem_reaches {D : DAG} {g r} : r ∈ D.reaches g ↔
    r ∈ D.roots ∧ Relation.ReflTransGen D.step (.row g) r.node := by
  classical
  exact Finset.mem_filter

theorem terminal {D : DAG} {r : Root} (hr : r ∈ D.roots) (v : Node) : ¬ D.step r.node v := by
  cases r with
  | arm b => exact id
  | ext j =>
    have hj : j ∈ D.extTops := by simpa [roots] using hr
    exact fun h => h.2.1 hj

theorem fork_iff {D : DAG} {g : ℕ} (present : g ∈ D.paidRows) (internal : g ∉ D.extTops) :
    Incidence.Fork D.step (.row g) ↔ 2 ≤ (D.readers g).card := by
  constructor
  · rintro ⟨a,b,ha,hb,hne⟩
    exact Finset.one_lt_card.mpr ⟨a,ha.2.2,b,hb.2.2,hne⟩
  · intro h
    obtain ⟨a,ha,b,hb,hne⟩ := Finset.one_lt_card.mp h
    exact ⟨a,b,⟨present,internal,ha⟩,⟨present,internal,hb⟩,hne⟩

theorem reaches_card_le_two {D : DAG} {g : ℕ}
    (fork : Incidence.Fork D.step (.row g)) (degree : (D.readers g).card ≤ 2)
    (antichain : ∀ {s t}, Incidence.Fork D.step s → Incidence.Fork D.step t → ¬ Relation.TransGen D.step s t) :
    (D.reaches g).card ≤ 2 := by
  classical
  let S := (D.reaches g).image Root.node
  have card : S.card = (D.reaches g).card := Finset.card_image_of_injective _ Root.node_injective
  rw [←card]
  apply Incidence.root_count D.step fork (D.readers g) S degree
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    obtain ⟨allowed,path⟩ := mem_reaches.mp hr
    rcases Relation.ReflTransGen.cases_head path with eq | ⟨v,hv,path'⟩
    · obtain ⟨a,_,ha,_,_⟩ := fork
      exact (terminal allowed a (eq ▸ ha)).elim
    · exact ⟨v,hv.2.2,hv,path'⟩
  · intro t ht
    obtain ⟨r,hr,rfl⟩ := Finset.mem_image.mp ht
    exact terminal (mem_reaches.mp hr).1
  · exact antichain

end DAG
end PEqualNP.Outside.L_meta_4186_aux.Q1Double.Virtual
