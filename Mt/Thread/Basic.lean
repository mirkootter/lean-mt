import Mt.Task
import Mt.Utils

namespace Mt

/-- A single thread of the system. It consists of a task to
  execute and a blocking predicate. The system only
  iterates a thread if the blocking predicate holds -/
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

/-- Small wrapper around `TaskM.valid`. A thread is considered valid
  if its underlying task is valid and ensures that it drops its
  reservation in the end.
  
  To prove `Thread.valid`, you should unfold `Thread.valid`, for example
  using `rw [Thread.valid]` and continue applying the validation theoreoms
  for `TaskM.valid`, like `TaskM.valid_bind` -/
def valid (thread : Thread spec) : Prop :=
  thread.task.valid IsReservation.empty
    thread.block_until
    (λ _ r => r = IsReservation.empty)

end Thread

end Mt