import Mt.Task
import Mt.Utils

namespace Mt

structure Thread (spec : Spec) where
  T : Type
  reservation : spec.Reservation
  block_until : spec.Reservation -> Bool
  task : TaskM spec T

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def mk_thread {T : Type} (task : TaskM spec T) : Thread spec := {
  T
  reservation := IsReservation.empty
  block_until :=λ _ => true
  task }

namespace Thread

inductive IterationResult (spec : Spec) where
  | Done : spec.Reservation -> spec.State -> IterationResult spec
  | Panic : spec.Reservation -> spec.State -> IterationResult spec
  | Running : spec.State -> Thread spec -> IterationResult spec

def IterationResult.state : IterationResult spec -> spec.State
  | Done _ state => state
  | Panic _ state => state
  | Running state _ => state

def IterationResult.reservation : IterationResult spec -> spec.Reservation
  | Done r _ => r
  | Panic r _ => r
  | Running _ cont => cont.reservation

def iterate : Thread spec -> spec.State -> IterationResult spec
  | ⟨T, r, _, task⟩, state =>
    match task.iterate r state with
    | TaskM.IterationResult.Done r state' _ => IterationResult.Done r state'
    | TaskM.IterationResult.Panic r state' _ => IterationResult.Panic r state'
    | TaskM.IterationResult.Running reservation state' block_until task => 
      IterationResult.Running state' { T, reservation, block_until, task }

def valid (thread : Thread spec) : Prop :=
  thread.task.valid thread.reservation
    thread.block_until
    (λ _ r => r = IsReservation.empty)

theorem valid.def (thread : Thread spec) :
  thread.valid = 
    ∀ env_r s,
    thread.block_until (env_r + thread.reservation) →
    spec.validate (env_r + thread.reservation) s →
    match thread.iterate s with
      | IterationResult.Done r' s' =>
          spec.validate (env_r + r') s' ∧
          r' = IsReservation.empty
      | IterationResult.Panic .. => False
      | IterationResult.Running s' cont =>
        (spec.validate (env_r + cont.reservation) s') ∧ cont.valid :=by
  simp only [valid]
  rw [TaskM.valid]
  
  apply Utils.forall_ext ; intro env_r
  apply Utils.forall_ext ; intro s
  rw [iterate]

  cases h : TaskM.iterate thread.task thread.reservation s
  <;> simp only [h]


end Thread

end Mt