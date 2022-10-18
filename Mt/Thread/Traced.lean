import Mt.Thread.Basic
import Mt.Utils

namespace Mt.Traced

structure TracedThread (spec : Spec) where
  thread : Thread spec
  reservation : spec.Reservation

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

namespace TracedThread

def T (t : TracedThread spec) : Type :=t.thread.T
def block_until (t : TracedThread spec) : spec.State -> Bool :=t.thread.block_until
def task (t : TracedThread spec) : TaskM spec t.T :=t.thread.task
def iterate (t : TracedThread spec) : spec.State -> Thread.IterationResult spec :=t.thread.iterate

def valid (thread : TracedThread spec) : Prop :=
  thread.thread.task.valid thread.reservation
    thread.thread.block_until
    (λ _ r => r = IsReservation.empty)

theorem valid_elim {thread : TracedThread spec}
  (is_valid : thread.valid)
  : ∀ env_r s,
    thread.block_until s →
    spec.validate (env_r + thread.reservation) s → ∃ r' : spec.Reservation,
    match thread.iterate s with
      | Thread.IterationResult.Done s' =>
          spec.validate (env_r + r') s' ∧
          r' = IsReservation.empty
      | Thread.IterationResult.Panic .. => False
      | Thread.IterationResult.Running s' cont =>
        (spec.validate (env_r + r') s') ∧ TracedThread.valid ⟨cont, r'⟩ :=by
  simp only [] -- TODO: Remove
  intro env_r s bu_true initial_valid
  rw [valid, TaskM.valid] at is_valid
  have :=is_valid env_r s bu_true initial_valid
  cases this

  clear is_valid ; rename_i r' is_valid
  exists r'
  simp only [iterate, Thread.iterate]
  
  cases h : TaskM.iterate thread.thread.task s
  all_goals (
    rw [h] at is_valid
    exact is_valid
  )

end TracedThread

end Mt.Traced