import Mt.Reservation
import Mt.Task.Basic

namespace Mt.TaskM

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

def valid {T : Type} (p : TaskM spec T) (r : spec.Reservation)
  (assuming : spec.Reservation -> Bool)
  (motive : T -> spec.Reservation -> spec.State -> Prop)
  : Prop :=∀ env_r s,
    assuming (env_r + r) →
    spec.validate (env_r + r) s →
    match h : p.iterate r s with
    | IterationResult.Done r' s' t => spec.validate (env_r + r') s' ∧ motive t r' s'
    | IterationResult.Panic .. => False
    | IterationResult.Running r' s' block_until cont =>
        spec.validate (env_r + r') s' ∧
        cont.valid r' block_until motive
termination_by valid => p
decreasing_by simp_wf ; exact is_direct_cont.running h

end Mt.TaskM