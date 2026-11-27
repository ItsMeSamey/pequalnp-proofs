import ExactPlaneCandidateCheck
namespace ExactPlaneExecutableSelector
open ExactPlanePhysicalConverse
variable {C I K B H : Type*}

def scan (prepare : C→Finset I) (valid : Finset I→Bool) : List C → Option (C × Finset I)
  | [] => none
  | g::gs =>
    let A := prepare g
    if valid A then some (g,A) else scan prepare valid gs

theorem scan_some {prepare : C→Finset I} {valid : Finset I→Bool} {charts : List C} {g : C} {A : Finset I}
    (h : scan prepare valid charts=some (g,A)) :
    ∃ pre post, charts=pre++g::post ∧ (∀ q∈pre,valid (prepare q)=false) ∧
      A=prepare g ∧ valid A=true := by
  induction charts with
  | nil => simp [scan] at h
  | cons x xs ih =>
    by_cases ok : valid (prepare x)=true
    · simp [scan,ok] at h
      obtain ⟨rfl,rfl⟩ := h
      exact ⟨[],xs,rfl,by simp,rfl,ok⟩
    · have no : valid (prepare x)=false := by cases ex : valid (prepare x) <;> simp_all
      have next : scan prepare valid xs=some (g,A) := by simpa [scan,no] using h
      obtain ⟨pre,post,eq,earlier,iss,good⟩ := ih next
      exact ⟨x::pre,post,by simp [eq],by
        intro q member
        rcases List.mem_cons.mp member with rfl|hmem
        · exact no
        · exact earlier q hmem,iss,good⟩

theorem scan_none (prepare : C→Finset I) (valid : Finset I→Bool) (charts : List C) :
    scan prepare valid charts=none ↔ ∀ g∈charts,valid (prepare g)=false := by
  induction charts with
  | nil => simp [scan]
  | cons g gs ih => cases h : valid (prepare g) <;> simp [scan,h,ih]

variable [Fintype I] [DecidableEq I] [AddCommGroup K] [Module F K] [DecidableEq K]
  [AddCommGroup B] [Module F B] [DecidableEq B] [AddCommGroup H] [Module F H] [DecidableEq H] [Fintype H]

def accept (read : C→I→B) (tag : I→B) (g : C) : Finset I :=
  Finset.univ.filter (fun i=>tag i=read g i)

def select (read : C→I→B) (priv : I→K) (tag : I→B) (height : I→H) (charts : List C) :=
  scan (accept read tag) (fun A=>ExactPlaneCandidateCheck.check A priv tag height) charts

theorem select_some {read : C→I→B} {priv : I→K} {tag : I→B} {height : I→H} {charts : List C}
    {g : C} {A : Finset I} (returned : select read priv tag height charts=some (g,A)) :
    ∃ pre post,charts=pre++g::post ∧
      (∀ q∈pre,¬ExactTrace priv tag height (accept read tag q)) ∧
      A=accept read tag g ∧ ExactTrace priv tag height A := by
  obtain ⟨pre,post,eq,no,ids,good⟩ := scan_some returned
  refine ⟨pre,post,eq,?_,ids,(ExactPlaneCandidateCheck.check_iff A priv tag height).mp good⟩
  intro q h t
  have on := (ExactPlaneCandidateCheck.check_iff _ priv tag height).mpr t
  have off := no q h
  simp [on] at off

theorem select_none (read : C→I→B) (priv : I→K) (tag : I→B) (height : I→H) (charts : List C) :
    select read priv tag height charts=none ↔ ∀ q∈charts,¬ExactTrace priv tag height (accept read tag q) := by
  rw [select,scan_none]
  simp only [←ExactPlaneCandidateCheck.check_iff,Bool.not_eq_true]
#print axioms select_some
#print axioms select_none
end ExactPlaneExecutableSelector
