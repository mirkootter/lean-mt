import Mt.System.Basic
import Mt.System.BasicAux
import Mt.System.Traced
import Mt.Utils.List

namespace Mt.System

variable {spec : Spec}
local instance : IsReservation spec.Reservation :=spec.is_reservation

open Utils

/-- Central validation predicate for reasoning about systems.

  A valid system has the following property: Given any future
  iteration of the system (or the system itself), the following
  holds:
  * No threads have panicked yet (and they never will)
  * The combination of state and thread reservations are valid
    according to the specification
-/
def valid (s : System spec) : Prop :=
  ∀ s' : System spec, s.reduces_to_or_eq s' →
  s'.panics = 0 ∧ ∃ r, spec.validate r s'.state

theorem fundamental_validation_theorem (s : System spec)
  (no_panics_yet : s.panics = 0)
  (initial_valid : spec.validate IsReservation.empty s.state)
  (threads_valid : ∀ t, t ∈ s.threads → t.valid)
  : s.valid :=by
  intro s' s_to_s'
  cases s_to_s' <;> rename_i h
  . rw [<- h]
    exact ⟨no_panics_yet, IsReservation.empty, initial_valid⟩
  
  let traced := Traced.TracedSystem.mk_initial s
  have traced_valid : traced.valid :=
    Traced.TracedSystem.mk_initial.valid s no_panics_yet initial_valid threads_valid

  sorry
end Mt.System