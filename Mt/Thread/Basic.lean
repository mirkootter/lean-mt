import Mt.Task
import Mt.Utils

namespace Mt

structure Thread (spec : Spec) where
  T : Type
  block_until : spec.State -> Bool
  task : TaskM spec T

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def mk_thread {T : Type} (task : TaskM spec T) : Thread spec := {
  T
  block_until :=λ _ => true
  task }

namespace Thread

inductive IterationResult (spec : Spec) where
  | Done : spec.State -> IterationResult spec
  | Panic : spec.State -> IterationResult spec
  | Running : spec.State -> Thread spec -> IterationResult spec

def IterationResult.state : IterationResult spec -> spec.State
  | Done state => state
  | Panic state => state
  | Running state _ => state

def iterate : Thread spec -> spec.State -> IterationResult spec
  | ⟨T, _, task⟩, state =>
    match task.iterate state with
    | TaskM.IterationResult.Done state' _ => IterationResult.Done state'
    | TaskM.IterationResult.Panic state' _ => IterationResult.Panic state'
    | TaskM.IterationResult.Running state' block_until task => 
      IterationResult.Running state' { T, block_until, task }

def valid (thread : Thread spec) : Prop :=
  ∃ r : spec.Reservation,
  thread.task.valid r
    thread.block_until
    (λ _ r => r = IsReservation.empty)

-- TODO: Remove? Probably not very useful
theorem valid_elim {thread : Thread spec}
  (is_valid : thread.valid)
  : ∃ r,
    ∀ env_r s,
    thread.block_until s →
    spec.validate (env_r + r) s → ∃ r' : spec.Reservation,
    match thread.iterate s with
      | IterationResult.Done s' =>
          spec.validate (env_r + r') s' ∧
          r' = IsReservation.empty
      | IterationResult.Panic .. => False
      | IterationResult.Running s' cont =>
        (spec.validate (env_r + r') s') ∧ cont.valid :=by
  simp only []
  cases is_valid ; rename_i r is_valid
  exists r
  intro env_r s bu_true initial_valid
  rw [TaskM.valid] at is_valid
  have is_valid :=is_valid env_r s bu_true initial_valid
  cases is_valid
  rename_i r' is_valid
  exists r'
  rw []
  simp only [iterate]
  cases h : TaskM.iterate thread.task s <;> simp only [h]
  . rw [h] at is_valid ; exact is_valid
  . rw [h] at is_valid ; contradiction
  . rw [h] at is_valid
    simp only [] at is_valid
    constructor
    . exact is_valid.left
    . simp only [valid]
      exists r'
      exact is_valid.right

end Thread

end Mt