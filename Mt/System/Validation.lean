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
    Traced.TracedSystem.mk_initial.valid s initial_valid threads_valid
  
  suffices ∃ ts : Traced.TracedSystem spec, ts.to_system = s' ∧ ts.valid by
    cases this
    rename_i ts ts_hyp
    simp only [<- ts_hyp.left, Traced.TracedSystem.to_system, true_and]
    exists ts.reservations
    exact ts_hyp.right.currently_valid
  
  clear initial_valid threads_valid
  
  suffices
    ∀ ts : Traced.TracedSystem spec, ts.valid →
    s = ts.to_system → ∃ ts' : Traced.TracedSystem spec, ts'.to_system = s' ∧ ts'.valid by
    apply this traced traced_valid
    exact Eq.symm <| Traced.TracedSystem.mk_initial.cancels_to_system no_panics_yet

  clear traced traced_valid no_panics_yet
  induction h
  . clear s s' ; rename_i s s' s_to_s'
    intro ts ts_valid s_def
    cases s_to_s'
    rename_i idx iteration
    exact Traced.TracedSystem.valid_by_iteration s s' s_def ts_valid iteration
  . rename_i a b c _ _ IHab IHbc
    intro ts_a ts_a_valid ts_a_hyp
    cases IHab ts_a ts_a_valid ts_a_hyp
    rename_i ts_b ts_b_hyp
    apply IHbc ts_b
    . exact ts_b_hyp.right
    . exact ts_b_hyp.left.symm

end Mt.System